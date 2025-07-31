From Stdlib Require Import String.
From EasyBakeCakeML.CakeML_Stdlib Require Import All.

Inductive LogLevel : Type :=
| Debug
| Info
| Warning
| Error
| Critical.

Definition log_le (l1 l2 : LogLevel) : bool :=
  match l1, l2 with
  | Debug, _ => true
  | _, Debug => false
  | Info, _ => true
  | _, Info => false
  | Warning, _ => true
  | _, Warning => false
  | Error, _ => true
  | _, Error => false
  | Critical, Critical => true
  end.

Lemma log_le_refl : forall l, log_le l l = true.
Proof.
  destruct l; simpl; auto.
Qed.

Lemma log_le_antisymm : forall l1 l2,
  log_le l1 l2 = true -> log_le l2 l1 = true -> l1 = l2.
Proof.
  destruct l1, l2; simpl; intros; try congruence.
Qed.

Lemma log_le_trans : forall l1 l2 l3,
  log_le l1 l2 = true -> 
  log_le l2 l3 = true -> 
  log_le l1 l3 = true.
Proof.
  destruct l1, l2, l3; simpl; eauto.
Qed.

Global Opaque log_le.

Definition log_level_str (level : LogLevel) : string :=
  match level with
  | Debug => "[DEBUG] "
  | Info => "[INFO] "
  | Warning => "[WARNING] "
  | Error => "[ERROR] "
  | Critical => "[CRITICAL] "
  end.
Global Opaque log_level_str.

Definition direct_log (level : LogLevel) (message : string) : unit :=
  match level with
  | Debug => TextIO.printLn_err (String.append (log_level_str Debug) message)
  | Info => TextIO.printLn_err (String.append (log_level_str Info) message)
  | Warning => TextIO.printLn_err (String.append (log_level_str Warning) message)
  | Error => TextIO.printLn_err (String.append (log_level_str Error) message)
  | Critical => TextIO.printLn_err (String.append (log_level_str Critical) message)
  end.
Global Opaque direct_log.

Definition log (print_level : LogLevel) (level : LogLevel) 
    (message : string) : unit :=
  if log_le print_level level 
  then direct_log level message
  else tt.
Global Opaque log.

Definition direct_log_debug (message : string) : unit :=
  direct_log Debug message.
Definition direct_log_info (message : string) : unit :=
  direct_log Info message.
Definition direct_log_warning (message : string) : unit :=
  direct_log Warning message.
Definition direct_log_error (message : string) : unit :=
  direct_log Error message.
Definition direct_log_critical (message : string) : unit :=
  direct_log Critical message.