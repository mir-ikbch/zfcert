module Kernel = Zfcert_kernel

let rec to_kernel = function
  | Syntax.Bottom -> Kernel.NFalsum
  | Syntax.Named (name, _) ->
      invalid_arg
        ("Unexpanded proposition alias reached the kernel: " ^ name)
  | Syntax.Eq (left, right) -> Kernel.NEqual (term_to_kernel left, term_to_kernel right)
  | Syntax.Mem (left, right) -> Kernel.NMember (term_to_kernel left, term_to_kernel right)
  | Syntax.Not formula -> Kernel.NNeg (to_kernel formula)
  | Syntax.And (left, right) ->
      Kernel.NConj (to_kernel left, to_kernel right)
  | Syntax.Or (left, right) ->
      Kernel.NDisj (to_kernel left, to_kernel right)
  | Syntax.Imp (left, right) ->
      Kernel.NImpl (to_kernel left, to_kernel right)
  | Syntax.Iff (left, right) ->
      Kernel.NIff (to_kernel left, to_kernel right)
  | Syntax.Forall (name, body) ->
      Kernel.NAll (name, to_kernel body)
  | Syntax.Exists (name, body) ->
      Kernel.NEx (name, to_kernel body)

and term_to_kernel = function
  | Syntax.Name name -> Kernel.NName name
  | Syntax.App (name, arguments) ->
      Kernel.NApp (name, arguments_to_kernel arguments)

and arguments_to_kernel = function
  | [] -> Kernel.NNNil
  | argument :: rest ->
      Kernel.NNCons (term_to_kernel argument, arguments_to_kernel rest)

let to_kernel_term = term_to_kernel

let rec of_kernel = function
  | Kernel.NFalsum -> Syntax.Bottom
  | Kernel.NEqual (left, right) ->
      Syntax.Eq (term_of_kernel left, term_of_kernel right)
  | Kernel.NMember (left, right) ->
      Syntax.Mem (term_of_kernel left, term_of_kernel right)
  | Kernel.NConj (left, right) ->
      Syntax.And (of_kernel left, of_kernel right)
  | Kernel.NDisj (left, right) ->
      Syntax.Or (of_kernel left, of_kernel right)
  | Kernel.NImpl (left, right) ->
      Syntax.Imp (of_kernel left, of_kernel right)
  | Kernel.NNeg formula -> Syntax.Not (of_kernel formula)
  | Kernel.NIff (left, right) ->
      Syntax.Iff (of_kernel left, of_kernel right)
  | Kernel.NAll (name, body) ->
      Syntax.Forall (name, of_kernel body)
  | Kernel.NEx (name, body) ->
      Syntax.Exists (name, of_kernel body)

and term_of_kernel = function
  | Kernel.NName name -> Syntax.Name name
  | Kernel.NApp (name, arguments) ->
      Syntax.App (name, arguments_of_kernel arguments)

and arguments_of_kernel = function
  | Kernel.NNNil -> []
  | Kernel.NNCons (argument, rest) ->
      term_of_kernel argument :: arguments_of_kernel rest

let of_kernel_term = term_of_kernel
