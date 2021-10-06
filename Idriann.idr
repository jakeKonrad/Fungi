module Idriann

import Data.Vect

data Tensor : Type where
  MkTensor : {dtype : Type} -> dtype -> List Nat -> Tensor

Tensors : Nat -> Type
Tensors n = Vect n Tensor

-- An extended version of the datatype presented in "An Initial Algebra Approach to
-- Directed Acyclic Graphs" by Jeremy Gibbons. Adapted to describe the flow of tensors
-- through a neural network.
data Graph : {m : Nat} -> {n : Nat} -> Tensors m -> Tensors n -> Type where
  Vert : (ms : Tensors m) -> (ns : Tensors n) -> Graph ms ns
  Edge : (x : Tensor) -> Graph [x] [x]
  Beside : Graph ms ns -> Graph ps qs -> Graph (ms ++ ps) (ns ++ qs)
  Before : Graph ms ns -> Graph ns ps -> Graph ms ps
  Empty : Graph [] []
  Swap : {m : Nat} 
      -> {n : Nat} 
      -> {ms : Tensors m} 
      -> {ns : Tensors n}
      -> Graph (ms ++ ns) (ns ++ ms)


