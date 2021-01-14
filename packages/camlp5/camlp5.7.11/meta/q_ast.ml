(* camlp5r *)
(* q_ast.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "pa_macro.cmo";
#load "pa_extend.cmo";
#load "q_MLast.cmo";

(* AST quotations that works by running the language parser (and its possible
   extensions) and meta-ifying the nodes. Works completely only in "strict"
   mode. In "transitional" mode, not all antiquotations are available. *)

value eval_anti entry loc typ str =
  let loc =
    let sh =
      if typ = "" then String.length "$"
      else
        String.length "$" + String.length typ + String.length ":"
    in
    let len = String.length str in
    Ploc.sub loc sh len
  in
  let r =
    try
      Ploc.call_with Plexer.force_antiquot_loc False
        (Grammar.Entry.parse entry) (Stream.of_string str)
    with
    [ Ploc.Exc loc1 exc ->
        let shift = Ploc.first_pos loc in
        let loc =
          Ploc.make_loc (Ploc.file_name loc)
            (Ploc.line_nb loc + Ploc.line_nb loc1 - 1)
            (if Ploc.line_nb loc1 = 1 then Ploc.bol_pos loc
             else shift + Ploc.bol_pos loc1)
            (shift + Ploc.first_pos loc1,
             shift + Ploc.last_pos loc1) ""
          in
          raise (Ploc.Exc loc exc) ]
  in
  (loc, r)
;

value skip_to_next_colon s i =
  loop (i + 1) where rec loop j =
    if j = String.length s then (i, 0)
    else
      match s.[j] with
      [ ':' -> (j, j - i - 1)
      | 'a'..'z' | 'A'..'Z' | '0'..'9' | '!' | '_' -> loop (j + 1)
      | _ -> (i, 0) ]
;

value get_anti_loc s =
  try
    let i = String.index s ':' in
    let (j, len) = skip_to_next_colon s i in
    let kind = String.sub s (i + 1) len in
    let loc =
      let k = String.index s ',' in
      let bp = int_of_string (String.sub s 0 k) in
      let ep = int_of_string (String.sub s (k + 1) (i - k - 1)) in
      Ploc.make_unlined (bp, ep)
    in
    Some (loc, kind, String.sub s (j + 1) (String.length s - j - 1))
  with
  [ Not_found | Failure _ -> None ]
;

module type MetaSig =
  sig
    type t = 'abstract;
    value loc_v : unit -> t;
    value node : string -> list t -> t;
    value node_no_loc : string -> list t -> t;
    value list : ('a -> t) -> list 'a -> t;
    value option : ('a -> t) -> option 'a -> t;
    value vala : ('a -> t) -> MLast.v 'a -> t;
    value bool : bool -> t;
    value string : string -> t;
    value tuple : list t -> t;
    value record : list (MLast.patt * t) -> t;
    value xtr : Ploc.t -> string -> t;
    value xtr_or_anti : Ploc.t -> (t -> t) -> string -> t;
  end
;

module Meta_make (C : MetaSig) =
  struct
    open MLast;
    value type_var (s, tv) =
      C.tuple [C.vala (C.option C.string) s; C.option C.bool tv]
    ;
    value record_label lab =
      let loc = Ploc.dummy in
      <:patt< MLast.$lid:lab$ >>
    ;
    value class_infos f ci =
      C.record
        [(record_label "ciLoc", C.loc_v ());
         (record_label "ciVir", C.vala C.bool ci.ciVir);
         (record_label "ciPrm",
          C.tuple [C.loc_v (); C.vala (C.list type_var) (snd ci.ciPrm)]);
         (record_label "ciNam", C.vala C.string ci.ciNam);
         (record_label "ciExp", f ci.ciExp)]
    ;
    value rec ctyp =
      fun
      [ TyAcc _ t1 t2 → C.node "TyAcc" [ctyp t1; ctyp t2]
      | TyAli _ t1 t2 → C.node "TyAli" [ctyp t1; ctyp t2]
      | TyAny _ → C.node "TyAny" []
      | TyApp _ t1 t2 → C.node "TyApp" [ctyp t1; ctyp t2]
      | TyArr _ t1 t2 → C.node "TyArr" [ctyp t1; ctyp t2]
      | TyCls _ ls → C.node "TyCls" [C.vala (C.list C.string) ls]
      | TyLab _ s t → C.node "TyLab" [C.vala C.string s; ctyp t]
      | TyLid _ s → C.node "TyLid" [C.vala C.string s]
      | TyMan _ t1 b t2 → C.node "TyMan" [ctyp t1; C.vala C.bool b; ctyp t2]
      | TyObj _ lst b →
          C.node "TyObj"
            [C.vala (C.list (fun (s, t) → C.tuple [C.string s; ctyp t])) lst;
             C.vala C.bool b]
      | TyOlb _ s t → C.node "TyOlb" [C.vala C.string s; ctyp t]
      | TyPck _ mt → C.node "TyPck" [module_type mt]
      | TyPol _ ls t → C.node "TyPol" [C.vala (C.list C.string) ls; ctyp t]
      | TyPot _ ls t → C.node "TyPot" [C.vala (C.list C.string) ls; ctyp t]
      | TyQuo _ s → C.node "TyQuo" [C.vala C.string s]
      | TyRec _ llsbt →
          C.node "TyRec"
            [C.vala
               (C.list
                  (fun (_, s, b, t) →
                     C.tuple [C.loc_v (); C.string s; C.bool b; ctyp t]))
               llsbt]
      | TySum _ llsltot →
          C.node "TySum"
            [C.vala
               (C.list
                  (fun (_, s, lt, ot) →
                     C.tuple
                       [C.loc_v (); C.vala C.string s;
                        C.vala (C.list ctyp) lt; C.option ctyp ot]))
               llsltot]
      | TyTup _ lt → C.node "TyTup" [C.vala (C.list ctyp) lt]
      | TyUid _ s → C.node "TyUid" [C.vala C.string s]
      | TyVrn _ lpv ools →
          C.node "TyVrn"
            [C.vala (C.list poly_variant) lpv;
             C.option (C.option (C.vala (C.list C.string))) ools]
      | 
          TyXtr loc s _ → C.xtr loc s ]
    and poly_variant =
      fun
      [ PvTag _ s b lt →
          C.node "PvTag"
            [C.vala C.string s; C.vala C.bool b; C.vala (C.list ctyp) lt]
      | PvInh _ t → C.node "PvInh" [ctyp t] ]
    and patt =
      fun
      [ PaAcc _ p1 p2 → C.node "PaAcc" [patt p1; patt p2]
      | PaAli _ p1 p2 → C.node "PaAli" [patt p1; patt p2]
      | PaAnt _ p → C.node "PaAnt" [patt p]
      | PaAny _ → C.node "PaAny" []
      | PaApp _ p1 p2 → C.node "PaApp" [patt p1; patt p2]
      | PaArr _ lp → C.node "PaArr" [C.vala (C.list patt) lp]
      | PaChr _ s → C.node "PaChr" [C.vala C.string s]
      | PaFlo _ s → C.node "PaFlo" [C.vala C.string s]
      | PaInt _ s1 s2 → C.node "PaInt" [C.vala C.string s1; C.string s2]
      | PaLab _ lpop →
          C.node "PaLab"
            [C.vala
               (C.list
                  (fun (p, op) → C.tuple [patt p; C.vala (C.option patt) op]))
               lpop]
      | PaLaz _ p → C.node "PaLaz" [patt p]
      | PaLid _ s → C.node "PaLid" [C.vala C.string s]
      | PaNty _ s → C.node "PaNty" [C.vala C.string s]
      | PaOlb _ p oe → C.node "PaOlb" [patt p; C.vala (C.option expr) oe]
      | PaOrp _ p1 p2 → C.node "PaOrp" [patt p1; patt p2]
      | PaRec _ lpp →
          C.node "PaRec"
            [C.vala (C.list (fun (p1, p2) → C.tuple [patt p1; patt p2])) lpp]
      | PaRng _ p1 p2 → C.node "PaRng" [patt p1; patt p2]
      | PaStr _ s → C.node "PaStr" [C.vala C.string s]
      | PaTup _ lp → C.node "PaTup" [C.vala (C.list patt) lp]
      | PaTyc _ p t → C.node "PaTyc" [patt p; ctyp t]
      | PaTyp _ ls → C.node "PaTyp" [C.vala (C.list C.string) ls]
      | PaUid _ s → C.node "PaUid" [C.vala C.string s]
      | PaUnp _ s omt →
          let c_vala x = C.vala C.string x in
          let c_vala_opt sopt = C.option c_vala sopt in
          C.node "PaUnp" [C.vala c_vala_opt s; C.option module_type omt]
      | PaVrn _ s → C.node "PaVrn" [C.vala C.string s]
      | 
          PaXtr loc s _ → C.xtr_or_anti loc (fun r → C.node "PaAnt" [r]) s ]
    and expr =
      fun
      [ ExAcc _ e1 e2 → C.node "ExAcc" [expr e1; expr e2]
      | ExAnt _ e → C.node "ExAnt" [expr e]
      | ExApp _ e1 e2 → C.node "ExApp" [expr e1; expr e2]
      | ExAre _ e1 e2 → C.node "ExAre" [expr e1; expr e2]
      | ExArr _ le → C.node "ExArr" [C.vala (C.list expr) le]
      | ExAsr _ e → C.node "ExAsr" [expr e]
      | ExAss _ e1 e2 → C.node "ExAss" [expr e1; expr e2]
      | ExBae _ e le → C.node "ExBae" [expr e; C.vala (C.list expr) le]
      | ExChr _ s → C.node "ExChr" [C.vala C.string s]
      | ExCoe _ e ot t → C.node "ExCoe" [expr e; C.option ctyp ot; ctyp t]
      | ExFlo _ s → C.node "ExFlo" [C.vala C.string s]
      | ExFor _ s e1 e2 b le →
          C.node "ExFor"
            [C.vala C.string s; expr e1; expr e2; C.vala C.bool b;
             C.vala (C.list expr) le]
      | ExFun _ lpoee →
          C.node "ExFun"
            [C.vala
               (C.list
                  (fun (p, oe, e) →
                     C.tuple [patt p; C.vala (C.option expr) oe; expr e]))
               lpoee]
      | ExIfe _ e1 e2 e3 → C.node "ExIfe" [expr e1; expr e2; expr e3]
      | ExInt _ s1 s2 → C.node "ExInt" [C.vala C.string s1; C.string s2]
      | ExJdf _ lx e → C.node "ExJdf" [C.vala (C.list joinclause) lx; expr e]
      | ExLab _ lpoe →
          C.node "ExLab"
            [C.vala
               (C.list
                  (fun (p, oe) → C.tuple [patt p; C.vala (C.option expr) oe]))
               lpoe]
      | ExLaz _ e → C.node "ExLaz" [expr e]
      | ExLet _ b lpe e →
          C.node "ExLet"
            [C.vala C.bool b;
             C.vala (C.list (fun (p, e) → C.tuple [patt p; expr e])) lpe;
             expr e]
      | ExLid _ s → C.node "ExLid" [C.vala C.string s]
      | ExLmd _ s me e →
          let c_vala x = C.vala C.string x in
          let c_vala_opt sopt = C.option c_vala sopt in
          C.node "ExLmd" [C.vala c_vala_opt s; module_expr me; expr e]
      | ExLop _ me e → C.node "ExLop" [module_expr me; expr e]
      | ExMat _ e lpoee →
          C.node "ExMat"
            [expr e;
             C.vala
               (C.list
                  (fun (p, oe, e) →
                     C.tuple [patt p; C.vala (C.option expr) oe; expr e]))
               lpoee]
      | ExNew _ ls → C.node "ExNew" [C.vala (C.list C.string) ls]
      | ExObj _ op lcsi →
          C.node "ExObj"
            [C.vala (C.option patt) op; C.vala (C.list class_str_item) lcsi]
      | ExOlb _ p oe → C.node "ExOlb" [patt p; C.vala (C.option expr) oe]
      | ExOvr _ lse →
          C.node "ExOvr"
            [C.vala (C.list (fun (s, e) → C.tuple [C.string s; expr e])) lse]
      | ExPar _ e1 e2 → C.node "ExPar" [expr e1; expr e2]
      | ExPck _ me omt →
          C.node "ExPck" [module_expr me; C.option module_type omt]
      | ExRec _ lpe oe →
          C.node "ExRec"
            [C.vala (C.list (fun (p, e) → C.tuple [patt p; expr e])) lpe;
             C.option expr oe]
      | ExRpl _ oe ls →
          C.node "ExRpl"
            [C.vala (C.option expr) oe;
             C.vala (fun (_, s) → C.tuple [C.loc_v (); C.vala C.string s]) ls]
      | ExSeq _ le → C.node "ExSeq" [C.vala (C.list expr) le]
      | ExSpw _ e → C.node "ExSpw" [expr e]
      | ExSnd _ e s → C.node "ExSnd" [expr e; C.vala C.string s]
      | ExSte _ e1 e2 → C.node "ExSte" [expr e1; expr e2]
      | ExStr _ s → C.node "ExStr" [C.vala C.string s]
      | ExTry _ e lpoee →
          C.node "ExTry"
            [expr e;
             C.vala
               (C.list
                  (fun (p, oe, e) →
                     C.tuple [patt p; C.vala (C.option expr) oe; expr e]))
               lpoee]
      | ExTup _ le → C.node "ExTup" [C.vala (C.list expr) le]
      | ExTyc _ e t → C.node "ExTyc" [expr e; ctyp t]
      | ExUid _ s → C.node "ExUid" [C.vala C.string s]
      | ExVrn _ s → C.node "ExVrn" [C.vala C.string s]
      | ExWhi _ e le → C.node "ExWhi" [expr e; C.vala (C.list expr) le]
      | 
          ExXtr loc s _ → C.xtr_or_anti loc (fun r → C.node "ExAnt" [r]) s ]
    and module_type =
      fun
      [ MtAcc _ mt1 mt2 → C.node "MtAcc" [module_type mt1; module_type mt2]
      | MtApp _ mt1 mt2 → C.node "MtApp" [module_type mt1; module_type mt2]
      | MtFun _ arg mt2 →
          let c_vala x = C.vala C.string x in
          let c_vala_opt sopt = C.option c_vala sopt in
          let c_tuple (sopt, mt) =
            C.tuple [C.vala c_vala_opt sopt; module_type mt] in
          let c_arg arg = C.option c_tuple arg in
            C.node "MtFun" [C.vala c_arg arg; module_type mt2]
      | MtLid _ s → C.node "MtLid" [C.vala C.string s]
      | MtQuo _ s → C.node "MtQuo" [C.vala C.string s]
      | MtSig _ lsi → C.node "MtSig" [C.vala (C.list sig_item) lsi]
      | MtTyo _ me → C.node "MtTyo" [module_expr me]
      | MtUid _ s → C.node "MtUid" [C.vala C.string s]
      | MtWit _ mt lwc →
          C.node "MtWit" [module_type mt; C.vala (C.list with_constr) lwc]
      | 
          MtXtr loc s _ → C.xtr loc s ]
    and sig_item =
      fun
      [ SgCls _ lcict →
          C.node "SgCls" [C.vala (C.list (class_infos class_type)) lcict]
      | SgClt _ lcict →
          C.node "SgClt" [C.vala (C.list (class_infos class_type)) lcict]
      | SgDcl _ lsi → C.node "SgDcl" [C.vala (C.list sig_item) lsi]
      | SgDir _ s oe →
          C.node "SgDir" [C.vala C.string s; C.vala (C.option expr) oe]
      | SgExc _ s lt →
          C.node "SgExc" [C.vala C.string s; C.vala (C.list ctyp) lt]
      | SgExt _ s t ls →
          C.node "SgExt"
            [C.vala C.string s; ctyp t; C.vala (C.list C.string) ls]
      | SgInc _ mt → C.node "SgInc" [module_type mt]
      | SgMod _ b lsmt →
          let c_vala x = C.vala C.string x in
          let c_vala_opt sopt = C.option c_vala sopt in
          C.node "SgMod"
            [C.vala C.bool b;
             C.vala
               (C.list
                  (fun (sopt, mt) → C.tuple [C.vala c_vala_opt sopt; module_type mt]))
               lsmt]
      | SgMty _ s mt → C.node "SgMty" [C.vala C.string s; module_type mt]
      | SgOpn _ ls → C.node "SgOpn" [C.vala (C.list C.string) ls]
      | SgTyp _ ltd → C.node "SgTyp" [C.vala (C.list type_decl) ltd]
      | SgUse _ s lsil →
          C.node "SgUse"
            [C.vala C.string s;
             C.vala (C.list (fun (si, _) → C.tuple [sig_item si; C.loc_v ()]))
               lsil]
      | SgVal _ s t → C.node "SgVal" [C.vala C.string s; ctyp t]
      | 
          SgXtr loc s _ → C.xtr loc s ]
    and with_constr =
      fun
      [ WcMod _ ls me →
          C.node "WcMod" [C.vala (C.list C.string) ls; module_expr me]
      | WcMos _ ls me →
          C.node "WcMos" [C.vala (C.list C.string) ls; module_expr me]
      | WcTyp _ ls ltv b t →
          C.node "WcTyp"
            [C.vala (C.list C.string) ls; C.vala (C.list type_var) ltv;
             C.vala C.bool b; ctyp t]
      | WcTys _ ls ltv t →
          C.node "WcTys"
            [C.vala (C.list C.string) ls; C.vala (C.list type_var) ltv;
             ctyp t] ]
    and module_expr =
      fun
      [ MeAcc _ me1 me2 → C.node "MeAcc" [module_expr me1; module_expr me2]
      | MeApp _ me1 me2 → C.node "MeApp" [module_expr me1; module_expr me2]
      | MeFun _ arg me →
          let c_vala x = C.vala C.string x in
          let c_vala_opt sopt = C.option c_vala sopt in
          let c_tuple (sopt, mt) =
            C.tuple [C.vala c_vala_opt sopt; module_type mt] in
          let c_arg arg = C.option c_tuple arg in
          C.node "MeFun" [C.vala c_arg arg; module_expr me]
      | MeStr _ lsi → C.node "MeStr" [C.vala (C.list str_item) lsi]
      | MeTyc _ me mt → C.node "MeTyc" [module_expr me; module_type mt]
      | MeUid _ s → C.node "MeUid" [C.vala C.string s]
      | MeUnp _ e omt → C.node "MeUnp" [expr e; C.option module_type omt]
      | 
          MeXtr loc s _ → C.xtr loc s ]
    and str_item =
      fun
      [ StCls _ lcice →
          C.node "StCls" [C.vala (C.list (class_infos class_expr)) lcice]
      | StClt _ lcict →
          C.node "StClt" [C.vala (C.list (class_infos class_type)) lcict]
      | StDcl _ lsi → C.node "StDcl" [C.vala (C.list str_item) lsi]
      | StDef _ lx → C.node "StDef" [C.vala (C.list joinclause) lx]
      | StDir _ s oe →
          C.node "StDir" [C.vala C.string s; C.vala (C.option expr) oe]
      | StExc _ s lt ls →
          C.node "StExc"
            [C.vala C.string s; C.vala (C.list ctyp) lt;
             C.vala (C.list C.string) ls]
      | StExp _ e → C.node "StExp" [expr e]
      | StExt _ s t ls →
          C.node "StExt"
            [C.vala C.string s; ctyp t; C.vala (C.list C.string) ls]
      | StInc _ me → C.node "StInc" [module_expr me]
      | StMod _ b lsme →
          let c_vala x = C.vala C.string x in
          let c_vala_opt sopt = C.option c_vala sopt in
          C.node "StMod"
            [C.vala C.bool b;
             C.vala
               (C.list
                  (fun (sopt, me) → C.tuple [C.vala c_vala_opt sopt; module_expr me]))
               lsme]
      | StMty _ s mt → C.node "StMty" [C.vala C.string s; module_type mt]
      | StOpn _ ls → C.node "StOpn" [C.vala (C.list C.string) ls]
      | StTyp _ b ltd →
          C.node "StTyp" [C.vala C.bool b; C.vala (C.list type_decl) ltd]
      | StUse _ s lsil →
          C.node "StUse"
            [C.vala C.string s;
             C.vala (C.list (fun (si, _) → C.tuple [str_item si; C.loc_v ()]))
               lsil]
      | StVal _ b lpe →
          C.node "StVal"
            [C.vala C.bool b;
             C.vala (C.list (fun (p, e) → C.tuple [patt p; expr e])) lpe]
      | 
          StXtr loc s _ → C.xtr loc s ]
    and joinclause x =
      C.record
        [(record_label "jcLoc", C.loc_v ());
         (record_label "jcVal",
          C.vala
            (C.list
               (fun (_, lllsop, e) →
                  C.tuple
                    [C.loc_v ();
                     C.vala
                       (C.list
                          (fun (_, ls, op) →
                             C.tuple
                               [C.loc_v ();
                                (fun (_, s) →
                                   C.tuple [C.loc_v (); C.vala C.string s])
                                  ls;
                                C.vala (C.option patt) op]))
                       lllsop;
                     expr e]))
            x.jcVal)]
    and type_decl x =
      C.record
        [(record_label "tdNam",
          C.vala (fun (_, s) → C.tuple [C.loc_v (); C.vala C.string s])
            x.tdNam);
         (record_label "tdPrm", C.vala (C.list type_var) x.tdPrm);
         (record_label "tdPrv", C.vala C.bool x.tdPrv);
         (record_label "tdDef", ctyp x.tdDef);
         (record_label "tdCon",
          C.vala (C.list (fun (t1, t2) → C.tuple [ctyp t1; ctyp t2]))
            x.tdCon)]
    and class_type =
      fun
      [ CtAcc _ ct1 ct2 → C.node "CtAcc" [class_type ct1; class_type ct2]
      | CtApp _ ct1 ct2 → C.node "CtApp" [class_type ct1; class_type ct2]
      | CtCon _ ct lt →
          C.node "CtCon" [class_type ct; C.vala (C.list ctyp) lt]
      | CtFun _ t ct → C.node "CtFun" [ctyp t; class_type ct]
      | CtIde _ s → C.node "CtIde" [C.vala C.string s]
      | CtSig _ ot lcsi →
          C.node "CtSig"
            [C.vala (C.option ctyp) ot; C.vala (C.list class_sig_item) lcsi]
      | 
          CtXtr loc s _ → C.xtr loc s ]
    and class_sig_item =
      fun
      [ CgCtr _ t1 t2 → C.node "CgCtr" [ctyp t1; ctyp t2]
      | CgDcl _ lcsi → C.node "CgDcl" [C.vala (C.list class_sig_item) lcsi]
      | CgInh _ ct → C.node "CgInh" [class_type ct]
      | CgMth _ b s t →
          C.node "CgMth" [C.vala C.bool b; C.vala C.string s; ctyp t]
      | CgVal _ b s t →
          C.node "CgVal" [C.vala C.bool b; C.vala C.string s; ctyp t]
      | CgVir _ b s t →
          C.node "CgVir" [C.vala C.bool b; C.vala C.string s; ctyp t] ]
    and class_expr =
      fun
      [ CeApp _ ce e → C.node "CeApp" [class_expr ce; expr e]
      | CeCon _ ls lt →
          C.node "CeCon"
            [C.vala (C.list C.string) ls; C.vala (C.list ctyp) lt]
      | CeFun _ p ce → C.node "CeFun" [patt p; class_expr ce]
      | CeLet _ b lpe ce →
          C.node "CeLet"
            [C.vala C.bool b;
             C.vala (C.list (fun (p, e) → C.tuple [patt p; expr e])) lpe;
             class_expr ce]
      | CeStr _ op lcsi →
          C.node "CeStr"
            [C.vala (C.option patt) op; C.vala (C.list class_str_item) lcsi]
      | CeTyc _ ce ct → C.node "CeTyc" [class_expr ce; class_type ct]
      | 
          CeXtr loc s _ → C.xtr loc s ]
    and class_str_item =
      fun
      [ CrCtr _ t1 t2 → C.node "CrCtr" [ctyp t1; ctyp t2]
      | CrDcl _ lcsi → C.node "CrDcl" [C.vala (C.list class_str_item) lcsi]
      | CrInh _ ce os →
          C.node "CrInh" [class_expr ce; C.vala (C.option C.string) os]
      | CrIni _ e → C.node "CrIni" [expr e]
      | CrMth _ b1 b2 s ot e →
          C.node "CrMth"
            [C.vala C.bool b1; C.vala C.bool b2; C.vala C.string s;
             C.vala (C.option ctyp) ot; expr e]
      | CrVal _ b1 b2 s e →
          C.node "CrVal"
            [C.vala C.bool b1; C.vala C.bool b2; C.vala C.string s; expr e]
      | CrVav _ b s t →
          C.node "CrVav" [C.vala C.bool b; C.vala C.string s; ctyp t]
      | CrVir _ b s t →
          C.node "CrVir" [C.vala C.bool b; C.vala C.string s; ctyp t] ]
    ;
  end
;

value anti_anti n = "_" ^ n;
value is_anti_anti n = String.length n > 0 && n.[0] = '_';

module Meta_E =
  Meta_make
    (struct
       type t = MLast.expr;
       value loc = Ploc.dummy;
       value loc_v () = <:expr< $lid:Ploc.name.val$ >>;
       value node con el =
         List.fold_left (fun e1 e2 -> <:expr< $e1$ $e2$ >>)
           <:expr< MLast.$uid:con$ $loc_v ()$ >> el
       ;
       value node_no_loc con el =
         List.fold_left (fun e1 e2 -> <:expr< $e1$ $e2$ >>)
           <:expr< MLast.$uid:con$ >> el
       ;
       value list elem el =
         loop el where rec loop el =
           match el with
           [ [] -> <:expr< [] >>
           | [e :: el] -> <:expr< [$elem e$ :: $loop el$] >> ]
       ;
       value option elem oe =
         match oe with
         [ None -> <:expr< None >>
         | Some e -> <:expr< Some $elem e$ >> ]
       ;
       value vala elem =
         IFNDEF STRICT THEN
           fun e -> elem e
         ELSE
           fun
           [ Ploc.VaAnt s ->
               match get_anti_loc s with
               [ Some (loc, typ, str) ->
                   let (loc, r) = eval_anti Pcaml.expr_eoi loc typ str in
                   if is_anti_anti typ then <:expr< $anti:r$ >>
                   else if not Pcaml.strict_mode.val then <:expr< $anti:r$ >>
                   else <:expr< Ploc.VaVal $anti:r$ >>
               | None -> assert False ]
           | Ploc.VaVal v ->
               if not Pcaml.strict_mode.val then elem v
               else <:expr< Ploc.VaVal $elem v$ >> ]
         END
       ;
       value bool b = if b then <:expr< True >> else <:expr< False >>;
       value string s = <:expr< $str:s$ >>;
       value tuple le = <:expr< ($list:le$) >>;
       value record lfe = <:expr< {$list:lfe$} >>;
       value xtr loc s =
         match get_anti_loc s with
         [ Some (_, typ, str) ->
             match typ with
             [ "" ->
                 let (loc, r) = eval_anti Pcaml.expr_eoi loc "" str in
                 <:expr< $anti:r$ >>
             | _ -> assert False ]
         | None -> assert False ]
       ;
       value xtr_or_anti loc f s =
         match get_anti_loc s with
         [ Some (_, typ, str) ->
             match typ with
             [ "" | "exp" ->
                 let (loc, r) = eval_anti Pcaml.expr_eoi loc typ str in
                 <:expr< $anti:r$ >>
             | "anti" ->
                 let (loc, r) = eval_anti Pcaml.expr_eoi loc "anti" str in
                 f <:expr< $anti:r$ >>
             | _ -> assert False ]
         | None -> assert False ]
       ;
     end)
;

module Meta_P =
  Meta_make
    (struct
       type t = MLast.patt;
       value loc = Ploc.dummy;
       value loc_v () = <:patt< _ >>;
       value node con pl =
         List.fold_left (fun p1 p2 -> <:patt< $p1$ $p2$ >>)
           <:patt< MLast.$uid:con$ _ >> pl
       ;
       value node_no_loc con pl =
         List.fold_left (fun p1 p2 -> <:patt< $p1$ $p2$ >>)
           <:patt< MLast.$uid:con$ >> pl
       ;
       value list elem el =
         loop el where rec loop el =
           match el with
           [ [] -> <:patt< [] >>
           | [e :: el] -> <:patt< [$elem e$ :: $loop el$] >> ]
       ;
       value option elem oe =
         match oe with
         [ None -> <:patt< None >>
         | Some e -> <:patt< Some $elem e$ >> ]
       ;
       value vala elem =
         IFNDEF STRICT THEN
           fun p -> elem p
         ELSE
           fun
           [ Ploc.VaAnt s ->
               match get_anti_loc s with
               [ Some (loc, typ, str) ->
                   let (loc, r) = eval_anti Pcaml.patt_eoi loc typ str in
                   if is_anti_anti typ then <:patt< $anti:r$ >>
                   else if not Pcaml.strict_mode.val then <:patt< $anti:r$ >>
                   else <:patt< Ploc.VaVal $anti:r$ >>
               | None -> assert False ]
           | Ploc.VaVal v ->
               if not Pcaml.strict_mode.val then elem v
               else <:patt< Ploc.VaVal $elem v$ >> ]
         END
       ;
       value bool b = if b then <:patt< True >> else <:patt< False >>;
       value string s = <:patt< $str:s$ >>;
       value tuple lp = <:patt< ($list:lp$) >>;
       value record lfp = <:patt< {$list:lfp$} >>;
       value xtr loc s =
         match get_anti_loc s with
         [ Some (_, typ, str) ->
             match typ with
             [ "" ->
                 let (loc, r) = eval_anti Pcaml.patt_eoi loc "" str in
                 <:patt< $anti:r$ >>
             | _ -> assert False ]
         | None -> assert False ]
       ;
       value xtr_or_anti loc f s =
         match get_anti_loc s with
         [ Some (_, typ, str) ->
             match typ with
             [ "" | "exp" ->
                 let (loc, r) = eval_anti Pcaml.patt_eoi loc "exp" str in
                 <:patt< $anti:r$ >>
             | "anti" ->
                 let (loc, r) = eval_anti Pcaml.patt_eoi loc "anti" str in
                 f <:patt< $anti:r$ >>
             | _ -> assert False ]
         | None -> assert False ]
       ;
     end)
;

value expr_eoi = Grammar.Entry.create Pcaml.gram "expr";
value patt_eoi = Grammar.Entry.create Pcaml.gram "patt";
value ctyp_eoi = Grammar.Entry.create Pcaml.gram "type";
value str_item_eoi = Grammar.Entry.create Pcaml.gram "str_item";
value sig_item_eoi = Grammar.Entry.create Pcaml.gram "sig_item";
value module_expr_eoi = Grammar.Entry.create Pcaml.gram "module_expr";
value module_type_eoi = Grammar.Entry.create Pcaml.gram "module_type";
value with_constr_eoi = Grammar.Entry.create Pcaml.gram "with_constr";
value poly_variant_eoi = Grammar.Entry.create Pcaml.gram "poly_variant";
value class_expr_eoi = Grammar.Entry.create Pcaml.gram "class_expr";
value class_type_eoi = Grammar.Entry.create Pcaml.gram "class_type";
value class_str_item_eoi = Grammar.Entry.create Pcaml.gram "class_str_item";
value class_sig_item_eoi = Grammar.Entry.create Pcaml.gram "class_sig_item";
value type_decl_eoi = Grammar.Entry.create Pcaml.gram "type_declaration";

EXTEND
  expr_eoi: [ [ x = Pcaml.expr; EOI -> x ] ];
  patt_eoi: [ [ x = Pcaml.patt; EOI -> x ] ];
  ctyp_eoi: [ [ x = Pcaml.ctyp; EOI -> x ] ];
  sig_item_eoi: [ [ x = Pcaml.sig_item; EOI -> x ] ];
  str_item_eoi: [ [ x = Pcaml.str_item; EOI -> x ] ];
  module_expr_eoi: [ [ x = Pcaml.module_expr; EOI -> x ] ];
  module_type_eoi: [ [ x = Pcaml.module_type; EOI -> x ] ];
  with_constr_eoi: [ [ x = Pcaml.with_constr; EOI -> x ] ];
  poly_variant_eoi: [ [ x = Pcaml.poly_variant; EOI -> x ] ];
  class_expr_eoi: [ [ x = Pcaml.class_expr; EOI -> x ] ];
  class_type_eoi: [ [ x = Pcaml.class_type; EOI -> x ] ];
  class_str_item_eoi: [ [ x = Pcaml.class_str_item; EOI -> x ] ];
  class_sig_item_eoi: [ [ x = Pcaml.class_sig_item; EOI -> x ] ];
  type_decl_eoi: [ [ x = Pcaml.type_decl; EOI -> x ] ];
END;

IFDEF STRICT THEN
  EXTEND
    Pcaml.expr: LAST
      [ [ s = ANTIQUOT_LOC "" -> MLast.ExXtr loc s None
        | s = ANTIQUOT_LOC "anti" -> MLast.ExXtr loc s None ] ]
    ;
    Pcaml.patt: LAST
      [ [ s = ANTIQUOT_LOC "" -> MLast.PaXtr loc s None
        | s = ANTIQUOT_LOC "anti" -> MLast.PaXtr loc s None ] ]
    ;
    Pcaml.ipatt: LAST
      [ [ s = ANTIQUOT_LOC "" -> MLast.PaXtr loc s None ] ]
    ;
    Pcaml.ctyp: LAST
      [ [ s = ANTIQUOT_LOC -> MLast.TyXtr loc s None ] ]
    ;
    Pcaml.str_item: FIRST
      [ [ s = ANTIQUOT_LOC -> MLast.StXtr loc s None
        | s = ANTIQUOT_LOC "exp" ->
            MLast.StExp loc (MLast.ExXtr loc s None) ] ]
    ;
    Pcaml.sig_item: FIRST
      [ [ s = ANTIQUOT_LOC -> MLast.SgXtr loc s None ] ]
    ;
    Pcaml.module_expr: LAST
      [ [ s = ANTIQUOT_LOC -> MLast.MeXtr loc s None ] ]
    ;
    Pcaml.module_type: LAST
      [ [ s = ANTIQUOT_LOC -> MLast.MtXtr loc s None ] ]
    ;
    Pcaml.class_expr: LAST
      [ [ s = ANTIQUOT_LOC -> MLast.CeXtr loc s None ] ]
    ;
    Pcaml.class_type: LAST
      [ [ s = ANTIQUOT_LOC -> MLast.CtXtr loc s None ] ]
    ;
  END;
END;

value check_anti_loc s =
  try
    let i = String.index s ':' in
    let (j, len) = skip_to_next_colon s i in
    String.sub s (i + 1) len
  with
  [ Not_found | Failure _ -> raise Stream.Failure ]
;

let lex = Grammar.glexer Pcaml.gram in
let tok_match = lex.Plexing.tok_match in
lex.Plexing.tok_match :=
  fun
  [("ANTIQUOT_LOC", p_prm) ->
      if p_prm <> "" && (p_prm.[0] = '~' || p_prm.[0] = '?') then
        let p_prm0 = p_prm.[0] in
        if p_prm.[String.length p_prm - 1] = ':' then
          let p_prm = String.sub p_prm 1 (String.length p_prm - 2) in
          fun
          [ ("ANTIQUOT_LOC", prm) ->
              if prm <> "" && prm.[0] = p_prm0 then
                if prm.[String.length prm - 1] = ':' then
                  let prm = String.sub prm 1 (String.length prm - 2) in
                  let kind = check_anti_loc prm in
                  if kind = p_prm || kind = anti_anti p_prm then prm
                  else raise Stream.Failure
                else raise Stream.Failure
              else raise Stream.Failure
          | _ -> raise Stream.Failure ]
        else
          let p_prm = String.sub p_prm 1 (String.length p_prm - 1) in
          fun
          [ ("ANTIQUOT_LOC", prm) ->
              if prm <> "" && prm.[0] = p_prm0 then
                if prm.[String.length prm - 1] = ':' then
                  raise Stream.Failure
                else
                  let prm = String.sub prm 1 (String.length prm - 1) in
                  let kind = check_anti_loc prm in
                  if kind = p_prm || kind = anti_anti p_prm then prm
                  else raise Stream.Failure
              else raise Stream.Failure
          | _ -> raise Stream.Failure ]
      else
        fun
        [ ("ANTIQUOT_LOC", prm) ->
            if prm <> "" && (prm.[0] = '~' || prm.[0] = '?') then
              raise Stream.Failure
            else
              let kind = check_anti_loc prm in
              if kind = p_prm then prm
              else raise Stream.Failure
        | _ -> raise Stream.Failure ]
  | ("V", p_prm) ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          let kind = check_anti_loc prm in
          if kind = p_prm || kind = anti_anti p_prm then prm
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V CHAR", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          let kind = check_anti_loc prm in
          if kind = "chr" || kind = anti_anti "chr" then prm
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V FLAG", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          let kind = check_anti_loc prm in
          if kind = "flag" || kind = anti_anti "flag" then prm
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V FLOAT", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          let kind = check_anti_loc prm in
          if kind = "flo" || kind = anti_anti "flo" then prm
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V INT", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          let kind = check_anti_loc prm in
          if kind = "int" || kind = anti_anti "int" then prm
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V INT_l", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          let kind = check_anti_loc prm in
          if kind = "int32" || kind = anti_anti "int32" then prm
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V INT_L", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          let kind = check_anti_loc prm in
          if kind = "int64" || kind = anti_anti "int64" then prm
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V INT_n", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          let kind = check_anti_loc prm in
          if kind = "nativeint" || kind = anti_anti "nativeint" then prm
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V LIDENT", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          if prm <> "" && (prm.[0] = '~' || prm.[0] = '?') then
            raise Stream.Failure
          else
            let kind = check_anti_loc prm in
            if kind = "lid" || kind = anti_anti "lid" then prm
            else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V LIST", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          let kind = check_anti_loc prm in
          if kind = "list" || kind = anti_anti "list" then prm
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V OPT", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          let kind = check_anti_loc prm in
          if kind = "opt" || kind = anti_anti "opt" then prm
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V QUESTIONIDENT", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          if prm <> "" && prm.[0] = '?' then
            if prm.[String.length prm - 1] = ':' then
              raise Stream.Failure
            else
              let prm = String.sub prm 1 (String.length prm - 1) in
              let kind = check_anti_loc prm in
              if kind = "" || kind = anti_anti "" then prm
              else raise Stream.Failure
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V QUESTIONIDENTCOLON", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          if prm <> "" && prm.[0] = '?' then
            if prm.[String.length prm - 1] = ':' then
              let prm = String.sub prm 1 (String.length prm - 2) in
              let kind = check_anti_loc prm in
              if kind = "" || kind = anti_anti "" then prm
              else raise Stream.Failure
            else raise Stream.Failure
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V STRING", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          if prm <> "" && (prm.[0] = '~' || prm.[0] = '?') then
            raise Stream.Failure
          else
            let kind = check_anti_loc prm in
            if kind = "str" || kind = anti_anti "str" then prm
            else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V TILDEIDENT", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          if prm <> "" && prm.[0] = '~' then
            if prm.[String.length prm - 1] = ':' then raise Stream.Failure
            else
              let prm = String.sub prm 1 (String.length prm - 1) in
              let kind = check_anti_loc prm in
              if kind = "" || kind = anti_anti "" then prm
              else raise Stream.Failure
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V TILDEIDENTCOLON", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          if prm <> "" && prm.[0] = '~' then
            if prm.[String.length prm - 1] = ':' then
              let prm = String.sub prm 1 (String.length prm - 2) in
              let kind = check_anti_loc prm in
              if kind = "" || kind = anti_anti "" then prm
              else raise Stream.Failure
            else raise Stream.Failure
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V UIDENT", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          if prm <> "" && (prm.[0] = '~' || prm.[0] = '?') then
            raise Stream.Failure
          else
            let kind = check_anti_loc prm in
            if kind = "uid" || kind = anti_anti "uid" then prm
            else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | tok -> tok_match tok ]
;

(* reinit the entry functions to take the new tok_match into account *)
Grammar.iter_entry Grammar.reinit_entry_functions
  (Grammar.Entry.obj Pcaml.expr);

value separate_locate s =
  let len = String.length s in
  if len > 0 && s.[0] = '@' then (String.sub s 1 (len - 1), True)
  else (s, False)
;

value apply_entry e me mp =
  let f s =
    Ploc.call_with Plexer.force_antiquot_loc True
      (Grammar.Entry.parse e) (Stream.of_string s)
  in
  let expr s =
    let (s, locate) = separate_locate s in
    me (f s)
  in
  let patt s =
    let (s, locate) = separate_locate s in
    let ast = mp (f s) in
    if locate then
      let (p, pl) =
        loop [] ast where rec loop pl =
          fun
          [ <:patt:< $p1$ $p2$ >> -> loop [(p2, loc) :: pl] p1
          | p -> (p, pl) ]
      in
      match pl with
      [ [(<:patt< _ >>, loc) :: pl] ->
          List.fold_left (fun p1 (p2, loc) -> <:patt< $p1$ $p2$ >>)
            <:patt< $p$ $lid:Ploc.name.val$ >> pl
      | _ -> ast ]
    else ast
  in
  Quotation.ExAst (expr, patt)
;

List.iter
  (fun (q, f) -> Quotation.add q f)
  [("expr", apply_entry expr_eoi Meta_E.expr Meta_P.expr);
   ("patt", apply_entry patt_eoi Meta_E.patt Meta_P.patt);
   ("ctyp", apply_entry ctyp_eoi Meta_E.ctyp Meta_P.ctyp);
   ("str_item", apply_entry str_item_eoi Meta_E.str_item Meta_P.str_item);
   ("sig_item", apply_entry sig_item_eoi Meta_E.sig_item Meta_P.sig_item);
   ("module_expr",
    apply_entry module_expr_eoi Meta_E.module_expr Meta_P.module_expr);
   ("module_type",
    apply_entry module_type_eoi Meta_E.module_type Meta_P.module_type);
   ("with_constr",
    apply_entry with_constr_eoi Meta_E.with_constr Meta_P.with_constr);
   ("poly_variant",
    apply_entry poly_variant_eoi Meta_E.poly_variant Meta_P.poly_variant);
   ("class_expr",
    apply_entry class_expr_eoi Meta_E.class_expr Meta_P.class_expr);
   ("class_type",
    apply_entry class_type_eoi Meta_E.class_type Meta_P.class_type);
   ("class_str_item",
    apply_entry class_str_item_eoi Meta_E.class_str_item
      Meta_P.class_str_item);
   ("class_sig_item",
    apply_entry class_sig_item_eoi Meta_E.class_sig_item
      Meta_P.class_sig_item);
   ("type_decl",
    apply_entry type_decl_eoi Meta_E.type_decl Meta_P.type_decl)]
;

do {
  let expr_eoi = Grammar.Entry.create Pcaml.gram "expr_eoi" in
  EXTEND
    expr_eoi:
      [ [ a = ANTIQUOT_LOC; EOI ->
            let loc = Ploc.make_unlined (0, 0) in
            if Pcaml.strict_mode.val then
              let a =
                let i = String.index a ':' in
                let i = String.index_from a (i + 1) ':' in
                let a = String.sub a (i + 1) (String.length a - i - 1) in
                Grammar.Entry.parse Pcaml.expr_eoi (Stream.of_string a)
              in
              <:expr< Ploc.VaAnt $anti:a$ >>
            else <:expr< failwith "antiquot" >>
        | e = Pcaml.expr; EOI ->
            let loc = Ploc.make_unlined (0, 0) in
            if Pcaml.strict_mode.val then <:expr< Ploc.VaVal $anti:e$ >>
            else <:expr< $anti:e$ >> ] ]
    ;
  END;
  let expr s =
    Ploc.call_with Plexer.force_antiquot_loc True
      (Grammar.Entry.parse expr_eoi) (Stream.of_string s)
  in
  let patt_eoi = Grammar.Entry.create Pcaml.gram "patt_eoi" in
  EXTEND
    patt_eoi:
      [ [ a = ANTIQUOT_LOC; EOI ->
            let loc = Ploc.make_unlined (0, 0) in
            if Pcaml.strict_mode.val then
              let a =
                let i = String.index a ':' in
                let i = String.index_from a (i + 1) ':' in
                let a = String.sub a (i + 1) (String.length a - i - 1) in
                Grammar.Entry.parse Pcaml.patt_eoi (Stream.of_string a)
              in
              <:patt< Ploc.VaAnt $anti:a$ >>
            else <:patt< _ >>
        | e = Pcaml.patt; EOI ->
            let loc = Ploc.make_unlined (0, 0) in
            if Pcaml.strict_mode.val then <:patt< Ploc.VaVal $anti:e$ >>
            else <:patt< $anti:e$ >> ] ]
    ;
  END;
  let patt s =
    Ploc.call_with Plexer.force_antiquot_loc True
      (Grammar.Entry.parse patt_eoi) (Stream.of_string s)
  in
  Quotation.add "vala" (Quotation.ExAst (expr, patt));
};
