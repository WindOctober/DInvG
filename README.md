# DInvG

## Docker Image

Prior to using this tool, users may download the precompiled Docker tar file (for the x86_64 platform) from the following link:

[Download Docker tar image](https://drive.google.com/file/d/1CaS17VoucpnJVaxpEM3agvbfqjKOs64h/view?usp=sharing)

After downloading, the image can be loaded using the following command:

```bash
docker load -i dinvg_x86_64.tar.gz
```

## Installation

After installing the aforementioned Docker image on the x86_64 platform, navigate to the working directory. In the project root directory on Ubuntu 20.04, compile and use the tool by executing the following commands:

```bash
mkdir build
cd build
cmake ..
make -jN
```

## Usage

The tool can be invoked as follows:

```bash
./bin/Inv sv path/to/file.c
```

Additionally, a Python script `scripts/exp.py` is provided in the project root to reproduce experimental results. To reproduce the data for Experiment 1 and Experiment 2, execute the following commands:

```bash
python scripts/exp.py           # Experiment 1: Data using the Propagation version
python scripts/exp.py --tool Inv_NoProp  # Experiment 2: Data using the non-Propagation version
```

The experimental results are recorded in the directories `./result/exp1/` and `./result/exp2/`, respectively.

**Note:** A minor issue is present in the `benchmark/VMCAI2019` directory. In previous experiments, an example correctly output the invariant using the Propagation version; however, subsequent modifications to Propagation resulted in an output of `Unknown`, while the non-Propagation version did not exhibit this bug. Consequently, in the associated publication, this example is temporarily marked as `Unknown`.

The discrepancy between the output and the actual results in two examples is primarily due to the fact that certain functions in SV-COMP, such as `nondet_char()`, have not yet been modeled in the current code implementation. The present code only models general numeric types, leading to an inaccurate range estimation.

## Experimental Environment

All experiments were conducted on a system with the following specifications:  
- **CPU:** 12th Gen Intel® Core™ i7-12800HX, 16 cores, 2304 MHz  
- **RAM:** 9.5 GB  
- **Operating System:** Ubuntu 20.04 LTS  

In accordance with the SV-COMP competition settings, a time limit of 900 seconds was imposed for both RQ1 and RQ2. In the experimental setup, only a single core was used for testing (the tool currently does not support parallel execution). The approximate runtime for RQ1 is 30–60 seconds and for RQ2 is 1800–2000 seconds (when executed on a single core).

## License

This project is licensed under the MIT License. Please refer to the LICENSE file for further details.

## Contact

Should you encounter any issues while using this tool, please submit them via GitHub Issues. If I fail to respond in a timely manner, feel free to contact me via email:

📧 **Email:** [Windocotber@sjtu.edu.cn](mailto:Windocotber@sjtu.edu.cn)

Thank you for your support and feedback!

---