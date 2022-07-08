----------------------------------------------------------------
-- The Agda standard library                                  --
--                                                            --
-- Library for (Generalized) Inference Systems                --
-- paper    : "Flexible Coinduction in Agda" @ ITP 2021       --
-- authors  : Luca Ciccone, Francesco Dagnino, Elena Zucca    --
-- doi      : https://doi.org/10.4230/LIPIcs.ITP.2021.13      --
-- examples : https://github.com/LcicC/inference-systems-agda --
----------------------------------------------------------------    

{-# OPTIONS --guardedness --without-K --safe #-}

-- Using Coinductive Records
module is-lib.InfSys {𝓁} where
 
  open import is-lib.InfSys.Base {𝓁} public 
  open import is-lib.InfSys.Induction {𝓁} public
  open import is-lib.InfSys.Coinduction {𝓁} public
  open import is-lib.InfSys.FlexCoinduction {𝓁} public
  open MetaRule public
  open FinMetaRule public
  open IS public