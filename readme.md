## General Information
This project displays an automated termination checker for integer transition systems. The integer transition system is inputted as an ARI-file. 

## Authors and License 
For further questions about the code or project contact christian.avery.weiss@rwth-aachen.de or leven@informatik.rwth-aachen.de. 
No license yet?


## Setup
With `lake build` the necessary dependencies can be built, so that the code can run locally on your device. For this the Z3-SMT solver has to be installed (https://theory.stanford.edu/~nikolaj/programmingz3.html). 


## Usage
With `lake exe check` the tool chain is executed. The toolchain reads the ITS-file which path is defined in `CheckAcyclic.lean` and gives the verdict whether it terminates.

## Understanding 
With `lake bild leantermination:docs` a documentation is generated. These can be viewed for example by using Python3x: `python3 -m http.server --directory .lake/build/doc`.
Further more in the code itself: there are comment blocks named `adr` (architectural design record). These records are more verbose than the code documentation. They are helpful to understand some more tricky proofs and come with some reasoning, why it was implemented in such way. Sometimes it gives notes, on what might need to change if the codebase would be extended. 
In the thesis **Automating Termination Proofs in Lean**, which can be found here (todo: insert link here) background on technique, proof strategy and related proofs is given which is the best way to familiarize.