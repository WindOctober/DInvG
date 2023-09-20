# StInGX Manual

The sections are as follows:
- Section 1: Getting Started Guide
- Section 2: Step by Step Instructions

This extension tool 'StInGX' has a low dependency for other library and is easy to install and use.

# 1 Getting Started Guide

We recommend you to use StInGX in Linux OS (such as Ubuntu 20.04 LTS or latest version, etc.).

The StInGX is depended on some libraries and let's firstly install them as follow:

## 1.1 Install the lib for PPL

The StInGX is depended on lib of PPL in version 1.2 (https://www.bugseng.com/ppl) and actually the PPL is depended on GMP yet.

Here are two method to install PPL, we recommend you to use the automatically install.

- ### Automatically install PPL 1.2 by Linux command (recommended)

The five libraries (GDB, GCC, M4, GMP, PPL) are all needed for running StInGX successfully.

Due to the dependency relation, we recommend you to execute command as following orders:

1. GDB: `sudo apt-get install gdb`
2. GCC: `sudo apt-get install gcc (or g++)`
3. M4 : `sudo apt-get install m4`
4. GMP: `sudo apt-get install libgmp10 libgmp-dev`
5. PPL: `sudo apt-get install ppl-dev`

- ### Mannually install PPL 1.2 by Official Website

You also can install them from official website.

1. GMP: https://gmplib.org/

2. PPL: https://www.bugseng.com/ppl

## 1.2 Test whether the PPL installation successfully

After you install all the depended libraries as above, you should be able to use the StInGX.

Try in the following command:

1. Open the tool directory: `cd StInGX`
2. Now, you can see binary file of StInGX named "lstingx" in current directory. Then run this binary without input: `./lstingx`
3. If you can see some output information (instead of error) as follows, then the StInGX could be used on your system! And you can skip section 1.3. (After run "lstingx" without input, you could run command `ctrl+c` to exit)

```
- Initialize_before_Parser doing...Done!

- ScanInput doing...
argc: 1
argv: ./lstingx
Done!
```

4. In case that the library is installed but StInGX (i.e. "lstingx") still could not run, you could remake the binary file of StInGX as explained in section 1.3.

## 1.3 Install the lib for Make

You could remake the binary file of StInGX "lstingx" by following command

1. Open the tool directory and you can see "Makefile": `cd StInGX`
2. Remake the binary file "lstingx" from file "Makefile" by command: `make`
3. If it outputs error when `make`, check the depended libraries (Bison, Flex, Makedepend) the `make` need.
4. You can install them by the following command:
   1. Bison: `sudo apt-get install bison`
   2. Flex: `sudo apt-get install flex`
   3. Makedepend: `sudo apt-get install xutils-dev`

# 2 Step by Step Instructions

After the Section 1, we can use StInGX as expectation.

Now, we will introduce how to reproduce our experimental results.



The basic operation to run binary file is in the following command (**you can skip these concrete command to reproduce data**):

- For original StInG (be used to comparison) command line

`../lstingx many < ${input_file} > ${output_file}`

- For Our Approach command line

```

../lstingx newdfs_sequences target_prior2 ${divide} ${projection} < ${input_file} > ${output_file}

For divide opinion: four_per_group, three_per_group, two_per_group, one_per_group

For projection opinion: KEC, FEC, REC, noProjection

```

If necessary, you can evaluate single file by single command line.



## 2.1 Reproduce the Data

To reproduce all the data, just follows the command:

1. Open the tool directory: `cd StInGX`
2. Open the "Examples" directory: `cd Examples`
3. Running: `../lstingx many < ${input_file} > ${output_file}`

After running over, we get all the data. 



```

----------------------------- 
| The Locations read in are: 
----------------------------- 

Location: l1
# of variables: 7
Initial Condition: [[ 
| 
...
| 
]]
Invariant: [[ 
| 
...
| 
]]

Location: l2
# of variables: 7
[ no initial condition set]
Invariant: [[ 
| 
...
| 
]]

/----------------------------- 
| Status after Solver: 
----------------------------- 
| # of Contexts generated = 23
| # pruned by inclusion tests in clumps = 10
| # pruned in Clump.cc = 0
| # of invariants *weav*ed = 7
| The collect_invariant Time Taken (0.01s) = 0
| # *bang*ed = 26
| The dfs_traverse Time Taken (0.01s) = 1
| Total Time taken (0.01s) = 5
\----------------------------- 

```



The invariant results is in `Invariant: [[ | ...| ]]`.

