# Parallel-CPCES
Parallel-CPCES is the concurrent version of probabilistic-CPCES-hit. Our paper is under review.

The introduction of probabilistic-CPCES-hit is at here: https://ojs.aaai.org/index.php/ICAPS/article/view/31532.

## Before Running
1. Download the classical planner FF and install it. Move the compiled executable `ff` to the `./classical_planner directory`. For more information about the FF planner, please refer to: https://fai.cs.uni-saarland.de/hoffmann/ff.html
2. You may need to install Madagascar planner. We provide an executable Madagascar under `classical_planner/DisjunctiveMadagascar` folder. Note that because Madagascar does not support disjunctive goals, we did some translations so that Madagascar can be run. The translation codes are under `classical_planner/DisjunctiveMadagascar/translate`
3. You may have to install some modules in `requirements.txt`.
4. Parallel-CPCES is a project built using **Django (version 4.2.11) + SQLite3 (version 3.31.1)**. Please install these dependencies before running the project. 
5. (***VERY IMPORTANT!!!***) This project requires python3 library NNF. After installing NNF module, find where NNF module is, and modify a file named `dsharp.py` (this file is in NNF module) at line 154. The original code is `return result`, but you should modify it as `return result, var_labels`. Our program uses var-labels to help us compute counter-tags.
6. Parallel-CPCES uses **Kissat** for computing hitting sets. You can download Kissat from https://github.com/arminbiere/kissat. After installation, place the folder `kissat-master` under pCPCES folder

## How to run Running Parallel-CPCES
You may need to set up some Django requirements before running. Please refer Django website to see how to set up Django.

To run Parallel-CPCES, execute the **run.py** file. (***very important !!!***) **Before each run, you must clear the SQLite database (if it exists) and the file system (if necessary).**

- Example Run Command:
  ```shell
  rm -f db.sqlite3
  rm -rf files
  python3 manage.py migrate
  python3 run.py -pl ff -p 4 -ht 2 -t 16 -m kissat -d pCPCES/FD-Benchmarks-0.90/dispose/domain.pddl -i pCPCES/FD-Benchmarks-0.90/dispose/instances/p_4_2.pddl
  
## Running Options
* -pl planner (ff or mad)
* -p the number of workers for ICTM and FCTM
* -ht the number of worker for HSM
* -t the number of worker for CTM
* -m hitting set tool (kissat or hitman)
* -d domain file path
* -i instance file path
