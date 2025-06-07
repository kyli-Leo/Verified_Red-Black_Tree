# Verified_Red-Black_Tree
Formally verified left-leaning red-black tree

## How is our code structured
`main.dfy` contains all driver code to perform a demo.  
`Lem.dfy` contains all lemmas used in verfication.  
`Type.dfy` contains the definition of `Color` and `Rb_tree`.  
`Operations.dfy` contains all our methods and is the most important part of our code.  
`Property.dfy` contains all predicates and functions that are used to define pre/post-conditions.  
`main-py` is a directory that contain all code that we translated from Dafny to Python.  
`main-py/test.py` is the unit test file for the Python code.



## How to run dafny code
To run our main method to demo a sample RRLB tree , go to our main directory and run `dafny run main.dfy`.

## How to run python unit test
To run python unit test, `cd main-py` and run `pytest test.py`