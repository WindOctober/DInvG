# VMCAI2025 AE

## Installation

After installing the released Docker image on the x86_64 platform, navigate to the working directory. In the project root directory on Ubuntu 20.04, compile and use the tool by executing the following commands:

```bash
mkdir build
cd build
cmake ..
make -jN # N is the number of available threads
```

## Usage

The tool can be used as follows:

```bash
./bin/Inv sv path/to/file.c
```

In the project root directory, a Python script `scripts/exp.py` is provided to reproduce the experimental results. Data reproduction for Experiment 1 and Experiment 2 is as follows:

```bash
python scripts/exp.py # Experiment 1: Data with Propagation version
python scripts/exp.py --tool Inv_NoProp # Experiment 2: Using non-Propagation version
```

The result of the experiment is recorded in ./result/exp1/ and ./result/exp2/.

**Note:** A minor error occurs in the `benchmark/VMCAI2019` directory. In previous experiments, an example was correctly outputting the invariant with the Propagation version. However, subsequent modifications to Propagation caused it to output `Unknown`, while the non-Propagation version did not exhibit this bug. Therefore, in the paper, this example is temporarily set to `Unknown`.

**The mismatch between the output and actual results in two examples is primarily due to the fact that some functions in SV-COMP, such as `nondet_char()`, have not yet been modeled in the code implementation. The code currently only models general numeric types, leading to incorrect range estimation.**

## Experimental Environment

All experiments are conducted on a machine equipped with a 12th Gen Intel(R) Core(TM) i7-12800HX CPU, 16 cores, 2304 MHz, 9.5 GB RAM, running Ubuntu 20.04 LTS. Following the competition settings of SV-COMP, a time limit of 900 seconds is imposed for studies RQ1 and RQ2.

In the specific experimental setup, only a single core was used for testing (the tool does not currently support parallelism). The approximate runtime for RQ1 is 30–60 seconds, and for RQ2 is 1800–2000 seconds (on a single core).

## License
This project is licensed under the MIT License. See the LICENSE file for details.

