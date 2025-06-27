From Stdlib Require Import String.
From EasyBakeCakeML Require Import CakeML_TextIO.

Inductive LogLevel : Type :=
| Debug
| Info
| Warning
| Error
| Critical.

Definition log_level_str (level : LogLevel) : string :=
  match level with
  | Debug => "[DEBUG] "
  | Info => "[INFO] "
  | Warning => "[WARNING] "
  | Error => "[ERROR] "
  | Critical => "[CRITICAL] "
  end.
Global Opaque log_level_str.

Definition log (level : LogLevel) (message : string) : unit :=
  match level with
  | Debug => TextIO.printLn_err (String.append (log_level_str Debug) message)
  | Info => TextIO.printLn_err (String.append (log_level_str Info) message)
  | Warning => TextIO.printLn_err (String.append (log_level_str Warning) message)
  | Error => TextIO.printLn_err (String.append (log_level_str Error) message)
  | Critical => TextIO.printLn_err (String.append (log_level_str Critical) message)
  end.
Global Opaque log.

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