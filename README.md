# INCPHP
inphp is a tool that generates different encodings of the pigeonhole
principle and uses an incremental satsolver, which supports the ipasir interface
to solve them incrementally.

## Preparation
Get a sat solver implementing the ipasir api.
I.e. from http://baldur.iti.kit.edu/sat-race-2015/downloads/ipasir.zip
Drop the sat solver library implementing the ipasir api in lib/ipasir

## Building
```
cd build
cmake ../src
make
```

The binaries will now be in bin/

## Experiments

To run the experiments you will need the python module
[experinemntRun](https://github.com/StephanGocht/experimentRun) as driver. Than
it is as simple as running python3 -m experimentRun experimentConfig.json

It might be neccessary to adjust the binary fiels in the configuration files.

Results submitted to SAT17 can be found in experiments/sat17

# Misc
Feel free to contact me if you have any problems or questions.