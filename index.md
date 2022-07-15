## Inference Systems in Agda 

An Agda library for (Generalized) Inference Systems.
Main ideas of the library are described in a paper presented at [ITP 2021](http://easyconferences.eu/itp2021/), available [here](https://drops.dagstuhl.de/opus/volltexte/2021/13908/). 
Check release notes for the compatibility with latest Agda and stdlib versions.

### How to use the library

1. Place ```is-lib``` inside your working directory.
2a. Import ```is-lib.InfSys``` to include inference systems, interpretations and proof principles
2b. Import ```is-lib.SInfSys``` to include inference systems, interpretations and proof principles using **sized types** (no --safe) 


### Content 

* Types for meta-rules and inference systems with composition operators (```is-lib/InfSys/Base.agda```) 
* Inductive interpretation, induction principle and properties (```is-lib/InfSys/Induction```) 
* Conductive interpretation, coinduction principle and properties (```is-lib/InfSys/Coinduction```) and variant with sized types (```is-lib/InfSys/SCoinduction```)
* Flexible conductive interpretation, bounded coinduction principle and properties (```is-lib/InfSys/FlexCoinduction```) and variant with sized types (```is-lib/InfSys/FlexSCoinduction```)
* Inference systems as Indexed (Endo)Containers and equivalence (```is-lib/InfSys/Container```)
* Examples: 
  * predicates on colists (```Examples/Colist```) 
  * big-step semantics of call-by-value lambda-calculus with divergence (```Examples/Lambda```)
* ```refactor-std-lib``` contains the library refactored to be used inside Agda standard library
  * Howto: place the content inside ```Data```  

#### Related projects 

* A formalization of properties of binary Session Types (including Fair Subtping). 
[code](https://github.com/boystrange/FairSubtypingAgda) [paper](https://drops.dagstuhl.de/opus/volltexte/2021/14194/) 

#### Authors 

* Luca Ciccone (Università di Torino)
* [Francesco Dagnino](https://fdgn.github.io/) (Università di Genova)
* [Elena Zucca](https://person.dibris.unige.it/zucca-elena/) (Università di Genova)
