# BranchCaRet Model Checking tool for Self-Modifying PDS.
Tool for BranchCaRet model checking Self-Modifying Pushdown Systems. This
is a tool for model checking SM-PDS against BranchCaRet formulas 
used in the paper "BranchCARET Model Checking of Self Modifying
Code". The repository contains the program with implementation
of BranchCARET model checking algorithm for pushdown systems:
 1. The standard implementation of Gutsfeld, Muller-Olm, and Nordhoff for PDS.
 2. The translation procedure from Self-Modifying PDS to standard PDS.
 3. The efficient algorithm for SM-PDS that avoids translation
    (our main contribution).


## Dependencies
 * linux
 * zig == 0.15.2
 * python 3

## Reproducing Experiments Table
Run:
```
python test.py
```
The script will populate table `results_stat.csv`. It was designed to
always generate the same input for each entry, so the results are
reproducible. The seed is generated from three variables of the table.
Then:
```
python table.py
```
The script will aggregate the data and print the LaTeX table used
in the paper.


## Usage Instructions
To build the binary:
```
./build.sh
```
There are two options for input: JSON and custom SM-PDS syntax. Examples of
different inputs can be found in `examples/` and `tests/`.
Full parsing logic can be found in `src/parser.zig`.

To model check on custom SM-PDS syntax:
```
./bcaret_mc_smpds <filename>
```

To model check on JSON:
```
./bcaret_mc_smpds -bin <filename>
```

To model check using a slow naive algorithm (for performance comparison),
use option `-naive`.
