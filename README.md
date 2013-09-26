probSAT
=======

The probSAT SAT Solver

An efficient implementation of a variant of the probSAT solver presented in:

"Choosing Probability Distributions for Stochastic Local Search and the Role of Make versus Break" by
Adrian Balint, Uwe Schöning

published in Lecture Notes in Computer Science, 2012, Volume 7317, Theory and Applications of Satisfiability Testing - SAT 2012, pages 16-29

This version does not track the make values of variables and is thus also not able to use them. 

=======
To build the solver run:

make

=======
To run the solver:

./probSAT instance.cnf <seed>

=======
The solver accepts a series of parameters which can be displayed by typing:

./probSAT -h