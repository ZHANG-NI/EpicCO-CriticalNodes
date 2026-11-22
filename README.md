# EpicCO: Critical Node Detection

The solver that [EpicCO](https://github.com/ZHANG-NI/EpicCO) produced for the critical node detection problem, starting from IRMS (Y. Zhou, J. Li, J.-K. Hao, and F. Glover, INFORMS Journal on Computing, 2024; https://github.com/INFORMSJoC/2022.0130).

## Run

```
mkdir -p bin
bash build.sh bin
bin/solver <instance> <solution> -t <seconds> -seed <seed>
```

The number of nodes to remove is read from a line `K <number>` appended to the instance file.
