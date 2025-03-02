# Parallel-CPCES

## Introduction

Parallel-CPCES is a project built using **Django (version 4.2.11) + SQLite3 (version 3.31.1)**. Please install these dependencies before running the project. 

Additionally, the following dependencies are required:

### 1. Classical Planner: Fast Forward (FF)
- Download and install the **Fast Forward (FF) planner**.
- Place the **ff executable** inside the `classical_planner` folder.

### 2. d-DNNF Compilation for Counter-Tag Set Probability Calculation
Parallel-CPCES uses **d-DNNF** to compute counter-tag set probabilities.

- This project uses the **NNF module** for compiling d-DNNF.
- After installing the **NNF module**, locate its installation directory and modify the file named `dsharp.py` at **line 154**.
- The original code:
  ```python
  return result
- The modified code:
  ```python
  return result, var_labels

### 3. Hitting Set Computation using Kissat
- Parallel-CPCES uses **Kissat** for computing hitting sets.
- You can download Kissat from https://github.com/arminbiere/kissat
- After installation, place the kissat project into pCPCES folder
- Ensure Kissat can be executed from: pCPCES/kissat-master/build/kissat

### 4. Running Parallel-CPCES
To run Parallel-CPCES, execute the **run.py** file. **Before each run, you must clear the SQLite database (if it exists) and the file system (if necessary).**

- Example Run Command:
  ```shell
  rm -f db.sqlite3
  rm -rf files
  python3 manage.py migrate
  python3 run.py -pl ff -p 4 -ht 2 -t 16 -m kissat -d pCPCES/FD-Benchmarks-0.90/dispose/domain.pddl -i pCPCES/FD-Benchmarks-0.90/dispose/instances/p_4_2.pddl