import os
import subprocess
import yaml
from tqdm import tqdm
import argparse
import resource
import time


def main():
    script_dir = os.path.dirname(os.path.abspath(__file__))
    project_root = os.path.abspath(os.path.join(script_dir, '../'))
    benchmark_dir = os.path.join(project_root, 'benchmark')
    bin_dir = os.path.join(project_root, 'bin')

    parser = argparse.ArgumentParser(
        description='Choose between Inv and Inv_NoProp')
    parser.add_argument(
        '--tool', choices=['Inv', 'Inv_NoProp'], default='Inv', help='Whether Propagation')
    args = parser.parse_args()

    inv_path = os.path.join(bin_dir, args.tool)

    if args.tool == 'Inv_NoProp':
        result_dir = os.path.join(project_root, 'result', 'exp2')
    else:
        result_dir = os.path.join(project_root, 'result', 'exp1')

    os.makedirs(result_dir, exist_ok=True)

    c_files = []
    stats = {}  # Per-directory statistics
    stats_per_parent = {}  # Per-parent-directory statistics
    total_stats = {'total': 0, 'consistent': 0,
                   'unknown': 0, 'wrong': 0, 'timeout': 0, 'time': 0.0}

    for subdir in ['SVComp', 'VMCAI2019']:
        current_benchmark = os.path.join(benchmark_dir, subdir)
        for root, dirs, files in os.walk(current_benchmark):
            for file in files:
                if file.endswith('.c'):
                    c_path = os.path.join(root, file)
                    rel_c_path = os.path.relpath(c_path, current_benchmark)
                    if subdir == 'SVComp':
                        first_level_dir = rel_c_path.split(os.sep)[0]
                        directory = first_level_dir  # Subdirectory under SVComp
                        parent_directory = 'SVComp'
                    else:
                        directory = 'VMCAI2019'
                        parent_directory = 'VMCAI2019'
                    c_files.append((directory, parent_directory, c_path))
                    if directory not in stats:
                        stats[directory] = {
                            'total': 0, 'consistent': 0, 'unknown': 0, 'wrong': 0, 'timeout': 0, 'time': 0.0}
                    if parent_directory not in stats_per_parent:
                        stats_per_parent[parent_directory] = {
                            'total': 0, 'consistent': 0, 'unknown': 0, 'wrong': 0, 'timeout': 0, 'time': 0.0}
    real_result = None
    for directory, parent_directory, c_path in tqdm(c_files, desc="Verify .c files", unit="file"):
        rel_path = os.path.relpath(c_path, benchmark_dir)
        stats[directory]['total'] += 1
        stats_per_parent[parent_directory]['total'] += 1
        total_stats['total'] += 1

        # Initialize variables
        tool_result = 'Unknown'
        comparison = 'Unknown'
        elapsed_time = 0.0

        # Function to set CPU time limit
        def limit_cpu():
            resource.setrlimit(resource.RLIMIT_CPU, (900, 900))

        try:
            start_time = time.time()
            proc = subprocess.run(
                [inv_path, 'sv', c_path],
                capture_output=True, text=True, preexec_fn=limit_cpu, timeout=900
            )
            elapsed_time = time.time() - start_time

            output = proc.stdout.strip()
            output_lines = output.split('\n')
            if output_lines:
                last_line = output_lines[-1].strip()
            else:
                last_line = ''

            if 'CORRECT' in last_line:
                tool_result = True
            elif 'WRONG' in last_line:
                tool_result = False
            else:
                tool_result = 'Unknown'
            comparison = 'Unknown'
        except subprocess.TimeoutExpired:
            elapsed_time = 900.0  # Since the timeout is 900 seconds
            last_line = ''
            tool_result = 'Unknown'
            comparison = 'Timeout'
            # Update timeout stats
            stats[directory]['timeout'] += 1
            stats_per_parent[parent_directory]['timeout'] += 1
            total_stats['timeout'] += 1

        if comparison == 'Timeout':
            pass
        elif tool_result == 'Unknown':
            stats[directory]['unknown'] += 1
            stats_per_parent[parent_directory]['unknown'] += 1
            total_stats['unknown'] += 1
        elif tool_result == real_result:
            stats[directory]['consistent'] += 1
            stats_per_parent[parent_directory]['consistent'] += 1
            total_stats['consistent'] += 1
        else:
            stats[directory]['wrong'] += 1
            stats_per_parent[parent_directory]['wrong'] += 1
            total_stats['wrong'] += 1

        if 'CORRECT' in last_line:
            tool_result = True
        elif 'WRONG' in last_line:
            tool_result = False
        else:
            tool_result = 'Unknown'
        if 'SVComp' in c_path:
            yml_path = os.path.splitext(c_path)[0] + '.yml'
            if os.path.exists(yml_path):
                with open(yml_path, 'r') as f:
                    data = yaml.safe_load(f)
                properties = data.get('properties', [])
                real_result = 'Unknown'
                for prop in properties:
                    if prop.get('property_file', '').endswith('unreach-call.prp'):
                        expected = prop.get('expected_verdict')
                        if isinstance(expected, bool):
                            real_result = expected
                        else:
                            real_result = 'Unknown'
                        break
                if real_result == 'Unknown':
                    print(
                        f"Exception: unreach-call.prp not found in {yml_path}")
            else:
                print(f"Exception: {yml_path} does not exist")
                real_result = 'Unknown'
        else:
            real_result = True

        # Update stats based on comparison
        if tool_result == 'Unknown':
            comparison = 'Unknown'
            stats[directory]['unknown'] += 1
            stats_per_parent[parent_directory]['unknown'] += 1
            total_stats['unknown'] += 1
        elif tool_result == real_result:
            comparison = 'Match'
            stats[directory]['consistent'] += 1
            stats_per_parent[parent_directory]['consistent'] += 1
            total_stats['consistent'] += 1
        else:
            comparison = 'Mismatch'
            stats[directory]['wrong'] += 1
            stats_per_parent[parent_directory]['wrong'] += 1
            total_stats['wrong'] += 1

        stats[directory]['time'] += elapsed_time
        stats_per_parent[parent_directory]['time'] += elapsed_time
        total_stats['time'] += elapsed_time

        # Write results to the .out file
        out_path = os.path.join(result_dir, rel_path.replace('.c', '.out'))
        os.makedirs(os.path.dirname(out_path), exist_ok=True)
        with open(out_path, 'w') as out_file:
            out_file.write(f"Tool Output: {tool_result}\n")
            if real_result is not None:
                out_file.write(f"Real Result: {real_result}\n")
            else:
                out_file.write("Real Result: Unknown\n")
            out_file.write(f"Comparison: {comparison}\n")
            out_file.write(f"Time Elapsed: {elapsed_time:.2f} seconds\n")

    # Write summary
    with open(os.path.join(result_dir, 'summary.txt'), 'w') as summary:
        # Per-directory statistics
        for directory in sorted(stats.keys()):
            summary.write(f"Directory: {directory}\n")
            summary.write(f"  Total Files: {stats[directory]['total']}\n")
            summary.write(f"  Consistent: {stats[directory]['consistent']}\n")
            summary.write(f"  Unknown: {stats[directory]['unknown']}\n")
            summary.write(f"  Wrong: {stats[directory]['wrong']}\n")
            summary.write(f"  Timeout: {stats[directory]['timeout']}\n")
            summary.write(
                f"  Total Time: {stats[directory]['time']:.2f} seconds\n\n")

        # Per-parent-directory statistics
        summary.write("Parent Directory Totals:\n")
        for parent_directory in sorted(stats_per_parent.keys()):
            summary.write(f"Parent Directory: {parent_directory}\n")
            summary.write(
                f"  Total Files: {stats_per_parent[parent_directory]['total']}\n")
            summary.write(
                f"  Consistent: {stats_per_parent[parent_directory]['consistent']}\n")
            summary.write(
                f"  Unknown: {stats_per_parent[parent_directory]['unknown']}\n")
            summary.write(
                f"  Wrong: {stats_per_parent[parent_directory]['wrong']}\n")
            summary.write(
                f"  Timeout: {stats_per_parent[parent_directory]['timeout']}\n")
            summary.write(
                f"  Total Time: {stats_per_parent[parent_directory]['time']:.2f} seconds\n\n")

        summary.write("Overall Totals:\n")
        summary.write(f"  Total Files: {total_stats['total']}\n")
        summary.write(f"  Consistent: {total_stats['consistent']}\n")
        summary.write(f"  Unknown: {total_stats['unknown']}\n")
        summary.write(f"  Wrong: {total_stats['wrong']}\n")
        summary.write(f"  Timeout: {total_stats['timeout']}\n")
        summary.write(f"  Total Time: {total_stats['time']:.2f} seconds\n\n")


if __name__ == "__main__":
    main()
