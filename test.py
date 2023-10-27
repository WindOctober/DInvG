import subprocess
import re

def get_time_from_stingx_diff():
    """Run the stingx_diff.sh script and extract user and system times using regex."""
    
    # Run the stingx_diff.sh script with the time command and capture the stderr output
    command = "/usr/bin/time -f \"%U + %S\" ./stingx_diff.sh"
    process = subprocess.Popen(command, shell=True, stderr=subprocess.PIPE, stdout=subprocess.DEVNULL)
    _, stderr = process.communicate()
    # Convert stderr to string
    output = stderr.decode('utf-8')

    user_time, sys_time = re.search(r"(\d+\.\d+) \+ (\d+\.\d+)", output).groups()
    print(user_time,sys_time)
    return float(user_time) + float(sys_time)

def main():
    runs = 10
    total_time = 0.0

    # Initialize the debug script
    subprocess.run("./debug.sh", shell=True)

    for _ in range(runs):
        total_time += get_time_from_stingx_diff()

    average_time = total_time / runs
    print(f"Average user+system CPU time over {runs} runs: {average_time:.2f} seconds")

if __name__ == "__main__":
    main()
