# Inference Systems in Agda 

An Agda library for inference systems

### How to use 

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


