(**
Programming Languages in Rocq - Data Structures Shared Infrastructure

This chapter introduces _data structures_ directly in Rocq, without
defining a new interpreted language.  The goal is to show how recursive
inductive types capture list structure, how higher-order functions
abstract over element-level operations, and why generalizing from
integer lists to polymorphic lists leaves every function's _structure_
unchanged.

The shared library here is intentionally minimal: unlike every prior
chapter, this one has no interpreter chain to import.  We simply
re-export the Rocq standard library modules used throughout.
 *)

From Stdlib Require Export Arith.
From Stdlib Require Export Bool.
From Stdlib Require Export Lia.
