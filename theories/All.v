From RocqCandy.Logging Require Export Logging_Axioms.
From Stdlib Require Import String.

Definition log_debug (message : string) : unit :=
  log Debug message.
Definition log_info (message : string) : unit :=
  log Info message.
Definition log_warning (message : string) : unit :=
  log Warning message.
Definition log_error (message : string) : unit :=
  log Error message.
Definition log_critical (message : string) : unit :=
  log Critical message.