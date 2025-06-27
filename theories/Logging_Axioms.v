(* 
  This file is meant to provide general purpose logging functions 
*)
From RocqCandy.Logging Require Export Logging_Types.
From Stdlib Require Import String.

Definition log (level : LogLevel) (message : string) : unit. Admitted.