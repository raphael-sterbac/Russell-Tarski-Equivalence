ty : Type
term : Type
lvl : Type

Prod : ty -> (bind ty in ty) -> ty
Lambda : ty -> ty -> (bind ty in term) -> term
App : ty -> ty -> term -> term -> term
Decode : lvl -> term -> ty

cProd: lvl -> term -> (bind term in term) -> term
cU: lvl -> lvl -> term
cLift: lvl -> lvl -> term -> term

U : lvl -> ty