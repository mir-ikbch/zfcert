(** Expand [input "filename".] commands without changing the proof environment.
    Each file is split into complete statements before it is included. *)
type loader = from:string option -> string -> string * string

type t

exception Error of int * string

(** [load_input ~from filename] returns a canonical filename and its contents.
    [from] is the filename of the source containing the command, when known.
    Input commands require an explicit loader; expansion itself does no I/O. *)
val expand : ?filename:string -> ?load_input:loader -> string -> t

(** Statement lines are internal identifiers. Use [error] to recover their
    original locations. *)
val statements : t -> (int * string) list

(** Report included-file errors at the outermost input command in the root
    script, adding the included filename and source line to the message. *)
val error : t -> int -> string -> int * string

(** Internal identifier for EOF of the last source contributing a statement. *)
val end_line : t -> int
