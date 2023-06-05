# AutoHyperQCore

This repository contains the core algorithm of [AutoHyperQ](https://autohyper.github.io/) - a model checker for HyperQPTL.
The corresponding publication is 

> Raven Beutner and Bernd Finkbeiner. Model Checking Omega-Regular Hyperproperties with AutoHyperQ. LPAR 2023

AutoHyperQ builds on

> Raven Beutner and Bernd Finkbeiner. AutoHyper: Explicit-State Model Checking for HyperLTL. TACAS 2023

## Dependencies

This library does not provide standalone functionality. To use the AutoHyperQ tool use the frontend which can be found at [autohyper.github.io/](https://autohyper.github.io/). 
This library uses the [FsOmegaLib](https://github.com/ravenbeutner/FsOmegaLib) library which must be located in the parent directory. 
