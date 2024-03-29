# Inference Systems in Agda 

An Agda library for inference systems.

Main ideas of the library are described in a paper presented at [ITP 2021](http://easyconferences.eu/itp2021/), available [here](https://drops.dagstuhl.de/opus/volltexte/2021/13908/). 

Check release notes for the compatibility with latest Agda and stdlib versions.

### How to use the library

Import ```is-lib.InfSys``` to include inference systems, interpretations and proof principles

Import ```is-lib.SInfSys``` to include inference systems, interpretations and proof principles using sized types 


### Content 
* Types for meta-rules and inference systems with composition operators (```is-lib/InfSys/Base.agda```) 
* Inductive interpretation, induction principle and properties (```is-lib/InfSys/Induction```) 
* Conductive interpretation, coinduction principle and properties (```is-lib/InfSys/Coinduction```) and variant with sized types (```is-lib/InfSys/SCoinduction```)
* Flexible conductive interpretation, bounded coinduction principle and properties (```is-lib/InfSys/FlexCoinduction```) and variant with sized types (```is-lib/InfSys/FlexSCoinduction```)
* Inference systems as Indexed (Endo)Containers and equivalence (```is-lib/InfSys/Container```)
* Examples: 
  * predicates on colists (```Examples/Colist```) 
  * big-step semantics of call-by-value lambda-calculus with divergence (```Examples/Lambda```) 

#### Related projects 
* A formalization of Fair Subtping in Agda. [code](https://github.com/boystrange/FairSubtypingAgda) [paper](https://drops.dagstuhl.de/opus/volltexte/2021/14194/) 

#### Authors 
* Luca Ciccone (Università di Torino)
* [Francesco Dagnino](https://fdgn.github.io/) (Università di Genova)
* [Elena Zucca](https://person.dibris.unige.it/zucca-elena/) (Università di Genova)

