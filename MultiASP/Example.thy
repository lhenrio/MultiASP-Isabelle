theory Example 
imports MultiASP
begin

(* simple examples *)

locale example1 =
fixes MSigex :: Signature
defines MSigex_def: "MSigex \<equiv> Method ''Int'' ''foo'' []"
fixes Mex :: Method
defines Mex_def: "Mex \<equiv> \<lparr> Method.MethSignature = MSigex, 
                          Method.LocalVariables = [(''Int'',  ''y''), (''Int'',  ''x'')],
                          Method.Body = [ ''x'' =\<^sub>A Expr(Val (ASPInt 3)), 
                                          ''y'' =\<^sub>A Expr(Var (Id  ''x'')+\<^sub>A(Val (ASPInt 1)))]
                        \<rparr>"
fixes Cex :: Class
defines Cex_def : "Cex \<equiv> \<lparr> Class.Name = ''barclass'', 
                        Class.Interfaces = [], 
                        Class.ClassParameters = [],
                        Class.StateVariables = [], 
                        Class.Methods = [Mex] \<rparr>"  
fixes Pex :: Program
defines Pex_def : "Pex \<equiv> Prog [] [Cex] [] []"
begin

lemma bind_test0: " Bind Pex l_\<alpha> ''barclass'' ''foo'' [] = 
        Some (l_\<alpha>,[ ''x'' \<mapsto> null,  ''y'' \<mapsto> null],
   [ ''x'' =\<^sub>A Expr(Val (ASPInt 3)),
     ''y'' =\<^sub>A Expr(Var (Id ''x'')+\<^sub>A(Val (ASPInt 1)))]) "
by (simp add: Bind_def Pex_def Cex_def Mex_def MSigex_def fetchClass_def fetchMethodInClass_def)


(* Serve [simp, intro!]: 
      "\<lbrakk>(Activities \<alpha>) = Some (AO l_\<alpha> \<sigma> Tasks (Rq@R#Rq')) ; R=(f,m,vl); 
        Ready R Tasks Rq; 
         (\<sigma> l_\<alpha>) = Some (Obj (obj,C));
        Bind P l_\<alpha> C m vl = (locs,s)\<rbrakk> 
          \<Longrightarrow> P\<turnstile>Cn Activities Futures 
                \<leadsto>Cn (Activities(\<alpha>\<mapsto> (AO l_\<alpha> \<sigma> (Tasks(R\<mapsto>[(locs,s)]))) (Rq@Rq'))) Futures" *)
lemma test0: "\<lbrakk>(Activities \<alpha>) = Some (AO l_\<alpha> \<sigma> Tasks (Rq@R#Rq')) ; R=(f,''foo'',[]); 
        \<forall> Q\<in>dom(Tasks). (R,Q)\<in>Compatible;\<forall> Q\<in>set Rq. (R,Q)\<in>Compatible; 
         (\<sigma> l_\<alpha>) = Some (Obj (o1, ''barclass''))
         \<rbrakk> 
          \<Longrightarrow> Pex \<turnstile> Cn Activities Futures \<leadsto>
              (Cn (Activities(\<alpha>\<mapsto> (AO l_\<alpha> \<sigma> 
       (Tasks(R\<mapsto>[( l_\<alpha>,
                   [ ''x'' \<mapsto> null,  ''y'' \<mapsto> null],
                   [ ''x'' =\<^sub>A Expr(Val (ASPInt 3)),
                      ''y'' =\<^sub>A Expr (Var (Id ''x'')+\<^sub>AVal (ASPInt (Suc 0)))])])) (Rq@Rq')))) Futures)"
apply (rule Serve)
by (auto simp add: bind_test0)



(* Next step: assign x+1 to y using
AssignLocal  [simp, intro!]: 
     "\<lbrakk>Activities \<alpha> = Some (AO l_\<alpha> \<sigma> Tasks Rq); 
       Tasks Q = Some ((locs,(x=\<^sub>AExpr e);;Stl)#EcL);
       x\<in>dom locs ; (e, locs, \<sigma>,v)\<in>EvalExpr
      \<rbrakk> 
      \<Longrightarrow> P\<turnstile>Cn Activities Futures 
           \<leadsto>Cn (Activities(\<alpha>\<mapsto> (AO l_\<alpha> \<sigma> (Tasks(Q\<mapsto>((locs(x\<mapsto>v),Stl)#EcL))) Rq)))  Futures" *)

(* First a few lemmas *)
lemma test_1_step0a: "\<lbrakk>(Activities \<alpha>) = Some (AO l_\<alpha> \<sigma> Tasks Rq) ; 
        Tasks R = Some(( l_\<alpha>,[ ''x'' \<mapsto> null, ''y'' \<mapsto> null],[
                    ''x'' =\<^sub>A Expr(Val (ASPInt 3)),
                    ''y'' =\<^sub>A
                    Expr (Var  (Id ''x'')+\<^sub>AVal (ASPInt (Suc 0)))])#[])  \<rbrakk> 
          \<Longrightarrow> Pex \<turnstile> Cn Activities Futures \<leadsto>
              (Cn (Activities(\<alpha>\<mapsto> (AO l_\<alpha> \<sigma> 
       (Tasks(R\<mapsto>(( l_\<alpha>, [''x'' \<mapsto> null, ''y'' \<mapsto> null]( ''x'' \<mapsto> ASPInt 3),
                   [ ''y'' =\<^sub>A Expr (Var  (Id ''x'')+\<^sub>AVal (ASPInt (Suc 0)))])#[]))) Rq))) Futures)"
(* needed to make EvalExpr and EvalValue rules intros, simp *)
by (rule AssignLocal, simp+)

lemma eval_prep_lem1a: "((Var (Id ''x'')+\<^sub>AVal (ASPInt (Suc 0))), l_this, 
          [ ''x'' \<mapsto> null, ''y'' \<mapsto> null, ''x'' \<mapsto> ASPInt 3], \<sigma>,ASPInt(3+1))\<in>EvalExpr"
by (rule EvalExpr.intros(5), simp+)


lemma test_1_step1a: "\<lbrakk>(Activities \<alpha>) = Some (AO l_\<alpha> \<sigma> Tasks Rq) ; 
        Tasks R = Some((l_\<alpha>,[ ''x'' \<mapsto> null,  ''y'' \<mapsto> null,  ''x'' \<mapsto> ASPInt 3],
                   [ ''y'' =\<^sub>A
                    Expr (Var (Id ''x'')+\<^sub>AVal (ASPInt (Suc 0)))])#[]) \<rbrakk> 
          \<Longrightarrow> Pex \<turnstile> Cn Activities Futures \<leadsto>
              (Cn (Activities(\<alpha>\<mapsto> (AO l_\<alpha> \<sigma> 
       (Tasks(R\<mapsto>((l_\<alpha>,[''x'' \<mapsto> null, ''y'' \<mapsto> null,  ''x'' \<mapsto> ASPInt 3]( ''y'' \<mapsto> ASPInt 4),
                   [])#[]))) Rq))) Futures)"

apply (rule AssignLocal)
apply assumption+
apply simp
apply (insert eval_prep_lem1a)
by simp

(* Second Similar lemma for second step again because of copies in Eval context *)
lemma test_1_step1: "\<lbrakk>(Activities \<alpha>) = Some (AO l_\<alpha> \<sigma> Tasks Rq) ; 
          Tasks R = Some((l_\<alpha>,[ ''y'' \<mapsto> null,  ''x'' \<mapsto> ASPInt 3],
                   [ ''y'' =\<^sub>A
                    Expr (Var (Id ''x'')+\<^sub>AVal (ASPInt (Suc 0)))])#[]) \<rbrakk> 
          \<Longrightarrow> Pex \<turnstile> Cn Activities Futures \<leadsto>
              (Cn (Activities(\<alpha>\<mapsto> (AO l_\<alpha> \<sigma> 
       (Tasks(R\<mapsto>((l_\<alpha>,[ ''y'' \<mapsto> null,  ''x'' \<mapsto> ASPInt 3](''y'' \<mapsto> ASPInt 4),
                   [])#[]))) Rq))) Futures)"

apply (rule AssignLocal)
apply assumption+
apply simp
apply (insert eval_prep_lem1a)
by simp

(* rules so far explored 
 Serve and AssignLocal
*)
end

(* method operating on a state example *)
locale example2 =
fixes MSigstex :: Signature
defines MSigstex_def: "MSigstex \<equiv> Method ''Int'' ''m'' []"
fixes m :: Method
defines m_def: "m \<equiv> \<lparr> Method.MethSignature = MSigstex, 
                          Method.LocalVariables = [],
                          Method.Body = [''x'' =\<^sub>A Expr(Val (ASPInt 3))]
                        \<rparr>"
fixes Cex :: Class
defines Cex_def : "Cex \<equiv> \<lparr> Class.Name = ''Cx'', 
                        Class.Interfaces = [], 
                        Class.ClassParameters = [],
                        Class.StateVariables = [(''x'', ''x'')], 
                        Class.Methods = [m] \<rparr>"  
fixes Pex :: Program
defines Pex_def : "Pex \<equiv> Prog [] [Cex] [] []"
begin

lemma bind_test0: " Bind Pex l_\<alpha> ''Cx'' ''m'' [] = 
       Some  (l_\<alpha>,empty,
   [''x'' =\<^sub>A Expr(Val (ASPInt 3))]) "
by (simp add: Bind_def Pex_def Cex_def m_def MSigstex_def fetchClass_def fetchMethodInClass_def)

lemma test2: "\<lbrakk>(Activities \<alpha>) = Some (AO l_\<alpha> \<sigma> Tasks (Rq@R#Rq')) ; R=(f,''m'',[]); 
        \<forall> Q\<in>dom(Tasks). (R,Q)\<in>Compatible;\<forall> Q\<in>set Rq. (R,Q)\<in>Compatible; 
         (\<sigma> l_\<alpha>) = Some (Obj (empty, ''Cx''))
         \<rbrakk> 
          \<Longrightarrow> Pex \<turnstile> Cn Activities Futures \<leadsto>
              (Cn (Activities(\<alpha>\<mapsto> (AO l_\<alpha> \<sigma> 
       (Tasks(R\<mapsto>[(l_\<alpha>,empty,
                   [''x'' =\<^sub>A Expr(Val (ASPInt 3))])])) (Rq@Rq')))) Futures)"
apply (rule Serve)
by (auto simp add: bind_test0)

(* AssignField  [simp, intro!]: 
     "\<lbrakk>Activities \<alpha> = Some (AO l_\<alpha> \<sigma> Tasks Rq); 
       Tasks Q = Some ((locs,(x=\<^sub>AExpr e);;Stl)#EcL);
       x\<notin>dom locs; locs(This) = Some (ObjRef l);
       \<sigma>(l) = Some (Obj obj);x\<in>dom(fst(obj));  
       (e, locs, \<sigma>,v)\<in>EvalExpr;
       \<sigma>'=\<sigma>(l\<mapsto>Obj (obj.[x]:=v))
      \<rbrakk> 
      \<Longrightarrow> P\<turnstile>Cn Activities Futures  *)

lemma test3: "\<lbrakk>(Activities \<alpha>) = Some (AO l_\<alpha> \<sigma> Tasks Rq) ; 
           Tasks R = Some((l, empty,
                   [ ''x'' =\<^sub>A Expr(Val (ASPInt 3))])#[]);
                \<sigma>(l) = Some (Obj obj); ''x''\<in>dom(fst(obj))  \<rbrakk> 
   \<Longrightarrow>   Pex \<turnstile> Cn Activities Futures \<leadsto>
       (Cn (Activities(\<alpha>\<mapsto> (AO l_\<alpha>  (\<sigma>(l\<mapsto>Obj (obj.[ ''x'']:= (ASPInt 3)))) (Tasks(R\<mapsto>((l,empty, [])#[]))) Rq))) Futures)"
by (rule AssignField, auto)
end

locale example3 =
fixes MS :: Signature
defines MS_def: "MS \<equiv> Method ''Int'' ''m'' []"
fixes m :: Method
defines m_def: "m \<equiv> \<lparr> Method.MethSignature = MS, 
                          Method.LocalVariables = [],
                          Method.Body = []
                        \<rparr>"
fixes Cex :: Class
defines Cex_def : "Cex \<equiv> \<lparr> Class.Name = ''Cx'', 
                        Class.Interfaces = [], 
                        Class.ClassParameters = [(''y'', ''y'')],
                        Class.StateVariables = [(''x'', ''x'')], 
                        Class.Methods = [m] \<rparr>"  
fixes Pex :: Program
defines Pex_def : "Pex \<equiv> Prog [] [Cex] [] []"
begin

(*
New  [simp, intro!]: 
     "\<lbrakk>Activities \<alpha> = Some (AO l_\<alpha> \<sigma> Tasks Rq); 
       Tasks Q = Some ((locs,(x=\<^sub>Anew C(el));;Stl)#EcL);
       fields P C=field_list; params P C=param_list; 
       l\<notin>dom \<sigma>; 
       length param_list = length el;length param_list = length value_list; 
       \<forall> i<length value_list . (el!i,locs,\<sigma>,value_list!i)\<in>EvalExpr ;
       \<sigma>'=\<sigma>(l\<mapsto> Obj (  (map_of (zip field_list (replicate (length field_list) null)))
                    ++ (map_of (zip param_list value_list)), C ))
      \<rbrakk>  
      (* new term to evaluate is artificially complex because obj ref has to be encapsulated in a value and an expression*)
      \<Longrightarrow> P\<turnstile>Cn Activities Futures 
           \<leadsto>Cn (Activities(\<alpha>\<mapsto> (AO l_\<alpha> \<sigma>' (Tasks(Q\<mapsto>((locs,(x=\<^sub>AExpr (Val (ObjRef l));;Stl))#EcL))) Rq)) ) Futures" |
 *)

lemma PexCxfields: " fields Pex ''Cx'' = [''x'']"
by (simp add: Bind_def Pex_def Cex_def fields_def fetchClass_def)

lemma PexCxparams: "params Pex ''Cx'' = [ ''y'']"; 
by (simp add: Bind_def Pex_def Cex_def params_def fetchClass_def)

lemma test3: "\<lbrakk> Activities \<alpha> = Some (AO l_\<alpha> \<sigma> Tasks Rq); 
       Tasks Q = Some ((l_this,locs,[(x=\<^sub>Anew ''Cx''([(Val (ASPInt 3))]))])#[]);
       l\<notin>dom \<sigma>; \<sigma>' = \<sigma>(l \<mapsto> Obj([ ''x''\<mapsto> null,  ''y'' \<mapsto> (ASPInt 3)], ''Cx'')) \<rbrakk> 
       \<Longrightarrow>  Pex \<turnstile>Cn Activities Futures 
           \<leadsto>Cn (Activities(\<alpha>\<mapsto> (AO l_\<alpha> \<sigma>' (Tasks(Q\<mapsto>([(l_this,locs,([x=\<^sub>AExpr (Val (ObjRef l))]))]))) Rq)) ) Futures"

apply (rule_tac value_list = "[(ASPInt 3)]" in New)
apply assumption+
apply (simp add: PexCxfields)
apply (simp add: PexCxparams)
apply assumption
by simp+

end

locale example4 =
fixes MS :: Signature
defines MS_def: "MS \<equiv> Method ''Int'' ''foo'' []"
fixes m :: Method
defines m_def: "m \<equiv> \<lparr> Method.MethSignature = MS, 
                          Method.LocalVariables = [],
                          Method.Body = [return (Var This)]
                        \<rparr>"
fixes Cex :: Class
defines Cex_def : "Cex \<equiv> \<lparr> Class.Name = ''Cx'', 
                        Class.Interfaces = [], 
                        Class.ClassParameters = [(''y'', ''y'')],
                        Class.StateVariables = [(''x'', ''x'')], 
                        Class.Methods = [m] \<rparr>"  
fixes Pex :: Program
defines Pex_def : "Pex \<equiv> Prog [] [Cex] [] []"
begin
(*
     NewActive  [simp, intro!]: 
     "\<lbrakk>Activities \<alpha> = Some (AO l_\<alpha> \<sigma> tasks Rq); 
       tasks Q = Some ((l_this,locs,(x=\<^sub>AnewActive C(el));;Stl)#EcL); 
       fields P C=field_list; params P C=param_list; 
       \<gamma>\<notin>dom Activities;       
       length param_list = length el;   length param_list = length value_list; 
       \<forall> i<length value_list . ((el!i,l_this,locs,\<sigma>,value_list!i)\<in>EvalExpr \<and> serialize (value_list!i) \<sigma> \<sigma>\<^sub>0) ;
        l\<notin>dom \<sigma>\<^sub>0;
       \<sigma>'=\<sigma>\<^sub>0(l\<mapsto> Obj (  (map_of (zip field_list (replicate (length field_list) null)))
                    ++ (map_of (zip param_list value_list)), C )) 
     \<rbrakk>   
        \<Longrightarrow> P\<turnstile>Cn Activities Futures 
             \<leadsto>Cn (Activities(\<alpha>\<mapsto> (AO l_\<alpha> \<sigma> (tasks(Q\<mapsto>((l_this,locs,(x=\<^sub>AExpr (Val (ActRef \<gamma>)));;Stl)#EcL))) Rq))
                             (\<gamma>\<mapsto> (AO l \<sigma>' empty [])))  Futures" |
       (* new term to evaluate is artificially complex because obj ref has to be encapsulated in a value and an expression*)
*)

lemma PexCxfields: " fields Pex ''Cx'' = [''x'']"
by (simp add: Bind_def Pex_def Cex_def fields_def fetchClass_def)

lemma PexCxparams: "params Pex ''Cx'' = [ ''y'']"; 
by (simp add: Bind_def Pex_def Cex_def params_def fetchClass_def)

lemma test4: "\<lbrakk> Activities \<alpha> = Some (AO l_\<alpha> \<sigma> Tasks Rq); 
       Tasks Q = Some ((l_this,locs,[(x=\<^sub>AnewActive ''Cx''([(Val (ASPInt 3))]))])#[]);
       \<gamma>\<notin>dom Activities;
       l\<notin>dom \<sigma>\<^sub>0; \<sigma>' = \<sigma>\<^sub>0(l \<mapsto> Obj([ ''x''\<mapsto> null,  ''y'' \<mapsto> (ASPInt 3)], ''Cx'')) \<rbrakk> 
       \<Longrightarrow>  Pex \<turnstile>Cn Activities Futures 
           \<leadsto>Cn (Activities(\<alpha>\<mapsto> (AO l_\<alpha> \<sigma> (Tasks(Q\<mapsto>([(l_this,locs,([x=\<^sub>AExpr (Val (ActRef \<gamma>))]))]))) Rq)) 
                (\<gamma>\<mapsto> (AO l \<sigma>' empty []))) Futures"

apply (rule_tac value_list = "[(ASPInt 3)]"  in NewActive)
apply assumption+
apply (simp add: PexCxfields)

apply (simp add: PexCxparams)
apply assumption
apply simp+
thm serialize.intros

apply (simp add: serialize.intros)
apply assumption
by force

end

locale example5 =
fixes MS :: Signature
defines MS_def: "MS \<equiv> Method ''Int'' ''m'' []"
fixes m :: Method
defines m_def: "m \<equiv> \<lparr> Method.MethSignature = MS, 
                          Method.LocalVariables = [],
                          Method.Body = [return(Val(ASPInt 3))]
                        \<rparr>"
fixes Cex :: Class
defines Cex_def : "Cex \<equiv> \<lparr> Class.Name = ''Cx'', 
                        Class.Interfaces = [], 
                        Class.ClassParameters = [(''y'', ''y'')],
                        Class.StateVariables = [(''x'', ''x'')], 
                        Class.Methods = [m] \<rparr>"  
fixes Pex :: Program
defines Pex_def : "Pex \<equiv> Prog [] [Cex] [] []"
begin

(*
InvkActive  [simp, intro!]: 
     "\<lbrakk>Activities \<alpha> = Some (AO l_\<alpha> \<sigma> tasks Rq); 
       Activities \<beta> = Some (AO l\<^sub>\<beta> \<sigma>\<^sub>\<beta> tasks\<^sub>\<beta> Rq\<^sub>\<beta>); 
       tasks Q = Some ((l_this,locs,x=\<^sub>A(e.\<^sub>Am(el));;Stl)#EcL);
       \<alpha>\<noteq>\<beta>;
       (e,lt,locs,\<sigma>,ActRef \<beta>)\<in>EvalExpr;
       f\<notin>dom Futures;      l\<notin>dom \<sigma>;
       length value_list = length el; 
       \<forall> i<length value_list . ((el!i,l_this,locs,\<sigma>,value_list!i)\<in>EvalExpr) ;
       serialize_and_rename_list \<sigma>\<^sub>\<beta> value_list \<sigma> value_list' \<sigma>\<^sub>P; 
        \<sigma>'=\<sigma>\<^sub>\<beta> ++ \<sigma>\<^sub>P
      \<rbrakk>  
      \<Longrightarrow> P\<turnstile>Cn Activities Futures 
          \<leadsto>Cn (Activities(\<alpha>\<mapsto> AO l_\<alpha> (\<sigma>(l\<mapsto>FutRef f)) (tasks(Q\<mapsto>((l_this,locs,x=\<^sub>AExpr (Val (ObjRef l));;Stl)#EcL))) Rq)
                             (\<beta>\<mapsto> AO l\<^sub>\<beta> \<sigma>' tasks\<^sub>\<beta> (Rq\<^sub>\<beta>@[(f,m,value_list')]) )) (Futures(f\<mapsto>Undefined))" |
*)
lemma PexCxfields: " fields Pex ''Cx'' = [''x'']"
by (simp add: Bind_def Pex_def Cex_def fields_def fetchClass_def)

lemma PexCxparams: "params Pex ''Cx'' = [ ''y'']"; 
by (simp add: Bind_def Pex_def Cex_def params_def fetchClass_def)

lemma test5: "\<lbrakk> Activities \<alpha> = Some (AO l_\<alpha> \<sigma> Tasks Rq); 
                Activities \<beta> = Some (AO l\<^sub>\<beta> \<sigma>\<^sub>\<beta> Tasks\<^sub>\<beta> Rq\<^sub>\<beta>); 
       Tasks Q = Some ((l_this,locs,[(x=\<^sub>AVal(ActRef \<beta>).\<^sub>An([(Val (ASPInt 3))]))])#[]);
       \<alpha>\<noteq>\<beta>;  f\<notin>dom Futures;  l\<notin>dom \<sigma> \<rbrakk> 
      \<Longrightarrow> P\<turnstile>Cn Activities Futures 
          \<leadsto>Cn (Activities(\<alpha>\<mapsto> (AO l_\<alpha> (\<sigma>(l\<mapsto>FutRef f)) (Tasks(Q\<mapsto>([(l_this,locs,([x=\<^sub>AExpr (Val (ObjRef l))]))]))) Rq))
                             (\<beta>\<mapsto> AO l\<^sub>\<beta> \<sigma>' Tasks\<^sub>\<beta> (Rq\<^sub>\<beta>@[(f,n,[(ASPInt 3)])]))) (Futures(f\<mapsto>Undefined))"
(*                             
      \<gamma>\<notin>dom Activities;
       l\<notin>dom \<sigma>\<^sub>0; \<sigma>' = \<sigma>\<^sub>0(l \<mapsto> Obj([ ''x''\<mapsto> null,  ''y'' \<mapsto> (ASPInt 3)], ''Cx'')) \<rbrakk> 
       \<Longrightarrow>  Pex \<turnstile>Cn Activities Futures 
           \<leadsto>Cn (Activities(\<alpha>\<mapsto> (AO l_\<alpha> \<sigma> (Tasks(Q\<mapsto>([(l_this,locs,([x=\<^sub>AExpr (Val (ActRef \<gamma>))]))]))) Rq)) 
                (\<gamma>\<mapsto> (AO l \<sigma>' empty []))) Futures"
*)
apply (rule_tac value_list = "[(ASPInt 3)]" in InvkActive)
apply assumption+
apply (simp add: PexCxfields)

apply (simp add: PexCxparams)
apply assumption
apply simp+

apply (simp add: serialize_and_rename_list_def serialize.intros check_subst_def)
apply auto
apply (rule_tac x = "%x. x" in exI)
apply force
oops
end

locale Boudol_ex =
fixes MSa MSb :: Signature
defines MSa_def: "MSa \<equiv> Method ''void'' ''ma'' []"
defines MSb_def: "MSb \<equiv> Method ''void'' ''mb'' []"
fixes ma mb :: Method
fixes PIN t r:: "char list"
defines ma_def: "ma \<equiv> \<lparr> Method.MethSignature = MSa, 
                          Method.LocalVariables = [],
                          Method.Body = [IF (Var (Id PIN) ==\<^sub>A Val (ASPInt 0)) THEN [t =\<^sub>A Expr(Val(ASPInt 0))]ELSE [t =\<^sub>A Expr(Val(ASPInt 1))], 
                                         (* do something  IF compatible with mb then mb can read t \<Rightarrow> information flow*)
                                        t =\<^sub>A Expr(Val(ASPInt 2)),
                                        return Val (ASPBool True)]
                        \<rparr>"
defines mb_def: "mb \<equiv> \<lparr> Method.MethSignature = MSb, 
                          Method.LocalVariables = [],
                          Method.Body = [IF (Var (Id t) ==\<^sub>A Val (ASPInt 0)) THEN [r =\<^sub>A Expr(Val(ASPInt 1))] ELSE [r =\<^sub>A Expr(Val(ASPInt 0))]]
                        \<rparr>"
fixes Cex :: Class
defines Cex_def : "Cex \<equiv> \<lparr> Class.Name = ''Cx'', 
                        Class.Interfaces = [], 
                        Class.ClassParameters = [],
                        Class.StateVariables = [(''x'', t),(''x'', r),(''x'', PIN)], 
                        Class.Methods = [ma, mb] \<rparr>"  
fixes Pex :: Program
defines Pex_def : "Pex \<equiv> Prog [] [Cex] [] []"
begin


end
