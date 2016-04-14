(*  Title:      MultiASP.thy
    Author:     Ludovic Henrio and Florian Kammuller
                2014

    Note:       Multi-active object formalisation
                For the moment methods and parameter bindings are done statically, 
                  without inheritance but with interfaces
                  this could be improved
*)
theory StoreDefinition imports Main AuxiliaryFunctions begin

type_synonym Location = nat
type_synonym VarName =  string
type_synonym ClassName = string

datatype Value = null | ObjRef Location (* Other values can be added here *)

type_synonym  Object = "(VarName\<rightharpoonup>Value) * ClassName"


datatype Storable = Obj  Object | StoredVal  Value (* Other storables can be added here *)

type_synonym Store = "Location\<rightharpoonup>Storable"

end
