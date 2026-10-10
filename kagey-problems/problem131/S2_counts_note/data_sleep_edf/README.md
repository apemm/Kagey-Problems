# Sleep-EDF telemetry hypnograms

The 44 files `ST*-Hypnogram.edf` are from the Sleep-EDF Database Expanded, version 1.0.0, on
PhysioNet (https://physionet.org/content/sleep-edfx/1.0.0/), folder `sleep-telemetry`. They hold
only the scored sleep stages. They are redistributed here unchanged under the Open Data Commons
Attribution License v1.0. `sums_local.txt` has their SHA256 sums as published by PhysioNet.

Please cite B. Kemp, A. H. Zwinderman, B. Tuk, H. A. C. Kamphuisen and J. J. L. Oberye, Analysis of
a sleep-dependent neuronal feedback loop: the slow-wave microcontinuity of the EEG, IEEE Trans.
Biomed. Eng. 47 (2000), 1185-1194, and A. L. Goldberger et al., PhysioBank, PhysioToolkit, and
PhysioNet, Circulation 101 (2000), e215-e220.

`results.json` is written by `../sleep_application.py --boot 60`.
