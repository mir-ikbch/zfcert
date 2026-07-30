module Kernel = Zfcert_kernel

let rec to_kernel = function
  | Syntax.Bottom -> Kernel.NFalsum
  | Syntax.Named (name, _) ->
      invalid_arg
        ("Unexpanded proposition definition reached the kernel: " ^ name)
  | Syntax.Eq (left, right) -> Kernel.NEqual (left, right)
  | Syntax.Mem (left, right) -> Kernel.NMember (left, right)
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

let rec of_kernel = function
  | Kernel.NFalsum -> Syntax.Bottom
  | Kernel.NEqual (left, right) -> Syntax.Eq (left, right)
  | Kernel.NMember (left, right) -> Syntax.Mem (left, right)
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
