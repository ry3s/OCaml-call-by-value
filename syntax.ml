type pattern = PInt  of int
             | PBool  of bool
             | PVar  of name
             | PTuple of pattern list
             | PNil
             | PCons of pattern * pattern
             | PUnderscore

and expr = EVar   of name
         | EValue of value
         | EBin   of bin_op * expr * expr
         | ETuple of expr list
         | ENil
         | ECons  of expr * expr
         | ELet   of pattern * expr * expr
         | EIf    of expr * expr * expr
         | EFun   of name * expr
         | EApp   of expr * expr
         | ERLet  of name * name * expr * expr
         | EMRLet of (name * name * expr) list * expr
         | EMatch of expr * (pattern * expr) list

and value = VInt  of int
          | VBool of bool
          | VTuple of value list
          | VNil
          | VCons of value * value
          | VFun  of name * expr * env
          | VRFun of name * name * expr * env
          | VMRFun of int * (name * name * expr) list * env

and bin_op = OpAdd | OpSub | OpMul | OpDiv | OpEq | OpLt

and env = (name * value) list

and name = string

type command = CExp   of expr
             | CLet   of pattern * expr
             | CRLet  of name * name * expr
             | CMRLet of (name * name * expr) list
             | CEnd
