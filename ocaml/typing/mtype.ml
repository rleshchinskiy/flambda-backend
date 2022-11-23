(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Xavier Leroy, projet Cristal, INRIA Rocquencourt           *)
(*                                                                        *)
(*   Copyright 1996 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* Operations on module types *)

open Asttypes
open Path
open Types

let rl_with = Option.is_some (Sys.getenv_opt "RL_WITH")
let rl_debugging = Option.is_some (Sys.getenv_opt "RL_DEBUGGING")

let rec scrape_lazy env mty =
  let open Subst.Lazy in
  match mty with
    MtyL_ident p ->
      begin try
        scrape_lazy env (Env.find_modtype_expansion_lazy p env)
      with Not_found ->
        mty
      end
  | _ -> mty

let scrape env mty =
  match mty with
    Mty_ident p ->
     Subst.Lazy.force_modtype (scrape_lazy env (MtyL_ident p))
  | _ -> mty

let freshen ~scope mty =
  Subst.modtype (Rescope scope) Subst.identity mty

let rec strengthen_lazy ~aliasable env mty p =
  let open Subst.Lazy in
  let mty' = match scrape_lazy env mty with
    MtyL_signature sg ->
      MtyL_signature(strengthen_lazy_sig ~aliasable env sg p)
  | MtyL_functor(Named (Some param, arg), res)
    when !Clflags.applicative_functors ->
      MtyL_functor(Named (Some param, arg),
        strengthen_lazy ~aliasable:false env res (Papply(p, Pident param)))
  | MtyL_functor(Named (None, arg), res)
    when !Clflags.applicative_functors ->
      let param = Ident.create_scoped ~scope:(Path.scope p) "Arg" in
      MtyL_functor(Named (Some param, arg),
        strengthen_lazy ~aliasable:false env res (Papply(p, Pident param)))
  | mty ->
      mty
  in
  if rl_debugging then (
    Format.printf "@[<hv 2>strengthen_lazy@ %a@ %a@]@."
      Printtyp.modtype
      (force_modtype mty)
      Printtyp.modtype
      (force_modtype mty')
  );
  mty'
    
and strengthen_lazy_sig' ~aliasable env sg p =
  let open Subst.Lazy in
  let add_with w = Option.map (fun ws -> w :: ws) in
  let strengthen_item (env, withs) = function
    | SigL_value(_, _, _) as sigelt ->
        ((env, withs), Some sigelt)
    | SigL_type(id, {type_kind=Type_abstract}, _, _)
      when Btype.is_row_name (Ident.name id) ->
        ((env, None), None)
    | SigL_type(id, decl, rs, vis) ->
        let (newdecl, newwiths) =
          match decl.type_manifest, decl.type_private, decl.type_kind with
            Some _, Public, _ -> (decl, withs)
          | Some _, Private, (Type_record _ | Type_variant _) -> (decl, withs)
          | _ ->
              let name = Pdot(p, Ident.name id) in
              let manif =
                Some(Btype.newgenty(Tconstr(name, decl.type_params, ref Mnil)))
              in
              let decl = if decl.type_kind = Type_abstract then
                    { decl with type_private = Public; type_manifest = manif }
                  else
                    { decl with type_manifest = manif }
              in
              (decl, add_with (Sig_with_type ([Ident.name id], name)) withs )
        in
        ((env, newwiths), Some (SigL_type(id, newdecl, rs, vis)))
    | SigL_typext _ as sigelt ->
        ((env, withs), Some sigelt)
    | SigL_module(id, pres, md, rs, vis) ->
        let name = Pdot(p, Ident.name id) in
        let str =
          strengthen_lazy_decl ~aliasable env md name
        in
        let env =
          Env.add_module_declaration_lazy ~update_summary:false id pres md env in
        let bind = Sig_with_module ([Ident.name id],name) in
        ((env, add_with bind withs), Some (SigL_module(id, pres, str, rs, vis)))
        (* Need to add the module in case it defines manifest module types *)
    | SigL_modtype(id, decl, vis) ->
        let newdecl =
          match decl.mtdl_type with
          | Some _ when not aliasable ->
              (* [not alisable] condition needed because of recursive modules.
                See [Typemod.check_recmodule_inclusion]. *)
              decl
          | _ ->
              {decl with mtdl_type = Some(MtyL_ident(Pdot(p,Ident.name id)))}
        in
        let env = Env.add_modtype_lazy ~update_summary:false id decl env in
        ((env, None), Some (SigL_modtype(id, newdecl, vis)))
        (* Need to add the module type in case it is manifest *)
    | SigL_class _ as sigelt ->
        ((env, withs), Some sigelt)
    | SigL_class_type _ as sigelt ->
        ((env, withs), Some sigelt)
  in
  let ((_, withs), items) = List.fold_left_map strengthen_item (env, Some []) sg in
  (Option.map List.rev withs, List.filter_map Fun.id items)

and strengthen_lazy_sig ~aliasable env sg p =
  let (nom, items) = Subst.Lazy.unfold_signature_once sg in
  let (withs, items) = strengthen_lazy_sig' ~aliasable env items p in
  (*
  let items = strengthen_lazy_sig' ~aliasable env items p in
  let withs = None in
  *)
  let sg' = Subst.Lazy.of_signature_items items in
  let sg' = match nom, withs with
    | Some (p, cs), Some ds -> Subst.Lazy.add_nominal (p, cs @ ds) sg'
    | _, _ -> sg'
  in
  if rl_debugging then (
    Format.printf "@[<hv 2>strengthen_lazy_sig %s@ %a@ %a@]@."
      (Printtyp.string_of_path p)
      Printtyp.modtype
      (Mty_signature (Subst.Lazy.force_signature sg))
      Printtyp.modtype
      (Mty_signature (Subst.Lazy.force_signature sg')));
  sg'

and strengthen_lazy_decl ~aliasable env md p =
  let open Subst.Lazy in
  match md.mdl_type with
  | MtyL_alias _ -> md
  | _ when aliasable -> {md with mdl_type = MtyL_alias p}
  | mty -> {md with mdl_type = strengthen_lazy ~aliasable env mty p}

let () = Env.strengthen := strengthen_lazy

let strengthen ~aliasable env mty p =
  let mty = strengthen_lazy ~aliasable env (Subst.Lazy.of_modtype mty) p in
  Subst.Lazy.force_modtype mty

let strengthen_decl ~aliasable env md p =
  let md = strengthen_lazy_decl ~aliasable env
             (Subst.Lazy.of_module_decl md) p in
  Subst.Lazy.force_module_decl md

let subst_constraint s = function
  | Sig_with_module (ns, p) -> Sig_with_module (ns, Subst.module_path s p)
  | Sig_with_type (ns, p) -> Sig_with_type (ns, Subst.type_path s p)

let rec constrain_modtype env constr ~aliasable = function
  | Mty_ident p ->
      let p = Env.normalize_modtype_path env p in
      let mty = Env.find_modtype_expansion p env in
      constrain_modtype env constr ~aliasable mty
  | Mty_alias p ->
      let p = Env.normalize_module_path (Some Location.none) env p in
      let mty = (Env.find_module p env).md_type in
      constrain_modtype env constr ~aliasable mty
  | Mty_signature sg ->
      let sg = if Option.is_some (Signature.get_nominal sg)
        then Signature.add_with constr sg
        else Signature.unpack sg |> List.map (constrain_sig_item env constr ~aliasable) |> Signature.pack
      in
      Mty_signature sg
  | Mty_functor _ -> assert false
and constrain_sig_item env constr ~aliasable item =
  match constr, item with
  | Sig_with_module ([s], p), Sig_module(id, pres, md, rs, vis) when Ident.name id = s ->
      if rl_debugging then (
      Format.printf "  replace module %s with %s @." s (Printtyp.string_of_path p));
      let mty = if aliasable
        then Mty_alias p
        else
          let p = Env.normalize_module_path (Some Location.none) env p in
          (Env.find_module p env).md_type
      in
      let md = { md with md_type = mty } in
      Sig_module(id, pres, md, rs, vis)
  | Sig_with_module (s :: ns, p), Sig_module(id, pres, md, rs, vis) when Ident.name id = s ->
      let md = { md with md_type = constrain_modtype env (Sig_with_module (ns,p)) ~aliasable md.md_type } in
      Sig_module(id, pres, md, rs, vis)
  | Sig_with_type (s :: ns, p), Sig_module(id, pres, md, rs, vis) when Ident.name id = s ->
      let md = { md with md_type = constrain_modtype env (Sig_with_type (ns,p)) ~aliasable md.md_type } in
      Sig_module(id, pres, md, rs, vis)
  | Sig_with_type ([s], p), Sig_type(id, decl, rs, vis) when Ident.name id = s ->
      if rl_debugging then (
        Format.printf "  replace type %s with %s @." s (Printtyp.string_of_path p)
      );
      let decl =
        match decl.type_manifest, decl.type_private, decl.type_kind with
          Some _, Public, _ -> decl
        | Some _, Private, (Type_record _ | Type_variant _) -> decl
        | _ ->
          (* let name = Pdot (p, Ident.name id) in *)
          let manif = 
                Some(Btype.newgenty(Tconstr(p, decl.type_params, ref Mnil)))
          in
          if decl.type_kind = Type_abstract then
            { decl with type_private = Public; type_manifest = manif }
          else
            { decl with type_manifest = manif }
      in
      Sig_type(id, decl, rs, vis)
      (*
      | SigL_type(id, decl, rs, vis) ->
        let (newdecl, newwiths) =
          match decl.type_manifest, decl.type_private, decl.type_kind with
            Some _, Public, _ -> (decl, withs)
          | Some _, Private, (Type_record _ | Type_variant _) -> (decl, withs)
          | _ ->
              let name = Pdot(p, Ident.name id) in
              let manif =
                Some(Btype.newgenty(Tconstr(name, decl.type_params, ref Mnil)))
              in
              let decl = if decl.type_kind = Type_abstract then
                    { decl with type_private = Public; type_manifest = manif }
                  else
                    { decl with type_manifest = manif }
              in
              (decl, add_with (Sig_with_type ([Ident.name id], name)) withs )
        in
        ((env, newwiths), Some (SigL_type(id, newdecl, rs, vis)))
      *)
  | _, sigelt -> sigelt

let unfold_signature env subst ~aliasable sg =
  let sg' = match Signature.get_nominal sg with
    | None -> Signature.unpack sg
    | Some (p, constrs) ->
        if rl_debugging then (
          Format.printf "@[<hv 2>unfolding %a@]@."
            Printtyp.modtype
            (Mty_signature sg));
        let p = Env.normalize_modtype_path env (Subst.modtype_path subst p) in
        match Env.find_modtype_expansion p env with
        | Mty_signature sg ->
            let items = Signature.unpack sg in
            let sg' =
              List.map (subst_constraint subst) constrs
              |> List.fold_left
                  (fun items constr ->
                    List.map (constrain_sig_item env constr ~aliasable) items)
                  items 
            in
            if rl_debugging then (
            Format.printf "@[<hv 2>unfolded to %a@]@."
              Printtyp.modtype
              (Mty_signature (Signature.pack sg')));
            sg'
        | mty ->
            Format.printf "@[<hv 2>unexpectedtly unfolded to %a@]@."
              Printtyp.modtype mty;
            assert false
  in
  if rl_with then sg' else Signature.unpack sg

let sig_make_manifest = Signature.map (function
  | (Sig_value _ | Sig_class _ | Sig_class_type _ | Sig_typext _) as t -> t
  | Sig_type (id,decl,rs,vis) ->
    let newdecl =
      match decl.type_manifest, decl.type_private, decl.type_kind with
        Some _, Public, _ -> decl
      | Some _, Private, (Type_record _ | Type_variant _) -> decl
      | _ ->
        let manif =
          Some (Btype.newgenty(Tconstr(Pident id, decl.type_params, ref Mnil)))
        in
        if decl.type_kind = Type_abstract then
          { decl with type_private = Public; type_manifest = manif }
        else
          { decl with type_manifest = manif }
    in
    Sig_type(Ident.rename id, newdecl, rs, vis)
  | Sig_module(id, pres, md, rs, vis) ->
    let md =
      match md.md_type with
      | Mty_alias _ -> md
      | _ -> {md with md_type = Mty_alias (Pident id)}
    in
    Sig_module(Ident.rename id, pres, md, rs, vis)
  | Sig_modtype(id, decl, vis) ->
    let newdecl =
      {decl with mtd_type =
                   match decl.mtd_type with
                   | None -> Some (Mty_ident (Pident id))
                   | Some _ -> decl.mtd_type }
    in
    Sig_modtype(Ident.rename id, newdecl, vis))

let rec make_aliases_absent pres mty =
  match mty with
  | Mty_alias _ -> Mp_absent, false, mty
  | Mty_signature sg ->
      let items = Signature.unpack sg in
      let items' = List.map make_aliases_absent_sig_item items in
      let changed = List.exists fst items' in
      let mty = if changed
        then Mty_signature (List.map snd items' |> Signature.pack)
        else mty
      in
      pres,
      changed,
      mty
  | Mty_functor(arg, res) ->
      let _, changed, res = make_aliases_absent Mp_present res in
      pres, changed, Mty_functor(arg, res)
  | mty ->
      pres, false, mty

and make_aliases_absent_sig_item =function
  | Sig_module(id, pres, md, rs, priv) ->
      let pres', changed, md_type = make_aliases_absent pres md.md_type in
      let changed = changed || pres <> pres' in
      let md = { md with md_type } in
      changed, Sig_module(id, pres', md, rs, priv)
  | sigelt -> false, sigelt
  
let scrape_for_type_of env pres mty =
  let rec loop env path mty =
    match mty, path with
    | Mty_alias path, _ -> begin
        try
          let md = Env.find_module path env in
          loop env (Some path) md.md_type
        with Not_found -> mty
      end
    | mty, Some path ->
        strengthen ~aliasable:false env mty path
    | _ -> mty
  in
  let pres, _,  mty' = make_aliases_absent pres (loop env None mty) in
  if rl_debugging then (
    Format.printf "@[<hv 2>scrape_for_type_of@ %a@ %a@]@."
      Printtyp.modtype mty
      Printtyp.modtype mty'
  );
  pres, mty'

(* In nondep_supertype, env is only used for the type it assigns to id.
   Hence there is no need to keep env up-to-date by adding the bindings
   traversed. *)

type variance = Co | Contra | Strict

let rec nondep_mty_with_presence env va ids pres mty =
  match mty with
    Mty_ident p ->
      begin match Path.find_free_opt ids p with
      | Some id ->
          let expansion =
            try Env.find_modtype_expansion p env
            with Not_found ->
              raise (Ctype.Nondep_cannot_erase id)
          in
          nondep_mty_with_presence env va ids pres expansion
      | None -> pres, mty
      end
  | Mty_alias p ->
      begin match Path.find_free_opt ids p with
      | Some id ->
          let expansion =
            try Env.find_module p env
            with Not_found ->
              raise (Ctype.Nondep_cannot_erase id)
          in
          nondep_mty_with_presence env va ids Mp_present expansion.md_type
      | None -> pres, mty
      end
  | Mty_signature sg ->
      let mty = Mty_signature(nondep_sig env va ids sg) in
      pres, mty
  | Mty_functor(Unit, res) ->
      pres, Mty_functor(Unit, nondep_mty env va ids res)
  | Mty_functor(Named (param, arg), res) ->
      let var_inv =
        match va with Co -> Contra | Contra -> Co | Strict -> Strict in
      let res_env =
        match param with
        | None -> env
        | Some param -> Env.add_module ~arg:true param Mp_present arg env
      in
      let mty =
        Mty_functor(Named (param, nondep_mty env var_inv ids arg),
                    nondep_mty res_env va ids res)
      in
      pres, mty

and nondep_mty env va ids mty =
  snd (nondep_mty_with_presence env va ids Mp_present mty)

and nondep_sig_item env va ids = function
  | Sig_value(id, d, vis) ->
      Sig_value(id,
                {d with val_type = Ctype.nondep_type env ids d.val_type},
                vis)
  | Sig_type(id, d, rs, vis) ->
      Sig_type(id, Ctype.nondep_type_decl env ids (va = Co) d, rs, vis)
  | Sig_typext(id, ext, es, vis) ->
      Sig_typext(id, Ctype.nondep_extension_constructor env ids ext, es, vis)
  | Sig_module(id, pres, md, rs, vis) ->
      let pres, mty = nondep_mty_with_presence env va ids pres md.md_type in
      Sig_module(id, pres, {md with md_type = mty}, rs, vis)
  | Sig_modtype(id, d, vis) ->
      begin try
        Sig_modtype(id, nondep_modtype_decl env ids d, vis)
      with Ctype.Nondep_cannot_erase _ as exn ->
        match va with
          Co -> Sig_modtype(id, {mtd_type=None; mtd_loc=Location.none;
                                 mtd_attributes=[]; mtd_uid = d.mtd_uid}, vis)
        | _  -> raise exn
      end
  | Sig_class(id, d, rs, vis) ->
      Sig_class(id, Ctype.nondep_class_declaration env ids d, rs, vis)
  | Sig_class_type(id, d, rs, vis) ->
      Sig_class_type(id, Ctype.nondep_cltype_declaration env ids d, rs, vis)

and nondep_sig env va ids sg =
  let scope = Ctype.create_scope () in
  let sg, env = Env.enter_signature ~scope sg env in
  Signature.map (nondep_sig_item env va ids) sg

and nondep_modtype_decl env ids mtd =
  {mtd with mtd_type = Option.map (nondep_mty env Strict ids) mtd.mtd_type}

let nondep_supertype env ids = nondep_mty env Co ids
let nondep_sig env ids = nondep_sig env Co ids
let nondep_sig_item env ids = nondep_sig_item env Co ids

let enrich_typedecl env p id decl =
  match decl.type_manifest with
    Some _ -> decl
  | None ->
    match Env.find_type p env with
    | exception Not_found -> decl
        (* Type which was not present in the signature, so we don't have
           anything to do. *)
    | orig_decl ->
        if decl.type_arity <> orig_decl.type_arity then
          decl
        else begin
          let orig_ty =
            Ctype.reify_univars env
              (Btype.newgenty(Tconstr(p, orig_decl.type_params, ref Mnil)))
          in
          let new_ty =
            Ctype.reify_univars env
              (Btype.newgenty(Tconstr(Pident id, decl.type_params, ref Mnil)))
          in
          let env = Env.add_type ~check:false id decl env in
          match Ctype.mcomp env orig_ty new_ty with
          | exception Ctype.Incompatible -> decl
              (* The current declaration is not compatible with the one we got
                 from the signature. We should just fail now, but then, we could
                 also have failed if the arities of the two decls were
                 different, which we didn't. *)
          | () ->
              let orig_ty =
                Btype.newgenty(Tconstr(p, decl.type_params, ref Mnil))
              in
              {decl with type_manifest = Some orig_ty}
        end

let rec enrich_modtype env p mty =
  match mty with
    Mty_signature sg -> Mty_signature (Signature.map (enrich_item env p) sg)
  | _ ->
      mty

and enrich_item env p = function
    Sig_type(id, decl, rs, priv) ->
      Sig_type(id,
                enrich_typedecl env (Pdot(p, Ident.name id)) id decl, rs, priv)
  | Sig_module(id, pres, md, rs, priv) ->
      Sig_module(id, pres,
                  {md with
                   md_type = enrich_modtype env
                       (Pdot(p, Ident.name id)) md.md_type},
                 rs,
                 priv)
  | item -> item

let rec type_paths env p mty =
  match scrape env mty with
    Mty_ident _ -> []
  | Mty_alias _ -> []
  | Mty_signature sg -> type_paths_sig env p (Signature.unpack sg)
  | Mty_functor _ -> []

and type_paths_sig env p = function
  | [] -> []
  | Sig_type(id, _decl, _, _) :: rem ->
      Pdot(p, Ident.name id) :: type_paths_sig env p rem
  | Sig_module(id, pres, md, _, _) :: rem ->
      type_paths env (Pdot(p, Ident.name id)) md.md_type @
      type_paths_sig (Env.add_module_declaration ~check:false id pres md env)
        p rem
  | Sig_modtype(id, decl, _) :: rem ->
      type_paths_sig (Env.add_modtype id decl env) p rem
  | (Sig_value _ | Sig_typext _ | Sig_class _ | Sig_class_type _) :: rem ->
      type_paths_sig env p rem


let rec no_code_needed_mod env pres mty =
  match pres with
  | Mp_absent -> true
  | Mp_present -> begin
      match scrape env mty with
        Mty_ident _ -> false
      | Mty_signature sg -> no_code_needed_sig env sg
      | Mty_functor _ -> false
      | Mty_alias _ -> false
    end

and no_code_needed_sig env sg = no_code_needed_sig_items env (Signature.unpack sg)

and no_code_needed_sig_items env = function
  | [] -> true
  | Sig_value(_id, decl, _) :: rem ->
      begin match decl.val_kind with
      | Val_prim _ -> no_code_needed_sig_items env rem
      | _ -> false
      end
  | Sig_module(id, pres, md, _, _) :: rem ->
      no_code_needed_mod env pres md.md_type &&
      no_code_needed_sig_items
        (Env.add_module_declaration ~check:false id pres md env) rem
  | (Sig_type _ | Sig_modtype _ | Sig_class_type _) :: rem ->
      no_code_needed_sig_items env rem
  | (Sig_typext _ | Sig_class _) :: _ ->
      false

let no_code_needed env mty = no_code_needed_mod env Mp_present mty

(* Check whether a module type may return types *)

let rec contains_type env = function
    Mty_ident path ->
      begin try match (Env.find_modtype path env).mtd_type with
      | None -> true (* PR#6427 *)
      | Some mty -> contains_type env mty
      with Not_found -> true
      end
  | Mty_signature sg ->
      contains_type_sig env sg
  | Mty_functor (_, body) ->
      contains_type env body
  | Mty_alias _ ->
      false

and contains_type_sig env = Signature.exists (contains_type_item env)

and contains_type_item env = function
    Sig_type (_,({type_manifest = None} |
                 {type_kind = Type_abstract; type_private = Private}),_, _)
  | Sig_modtype _
  | Sig_typext (_, {ext_args = Cstr_record _}, _, _) ->
      (* We consider that extension constructors with an inlined
         record create a type (the inlined record), even though
         it would be technically safe to ignore that considering
         the current constraints which guarantee that this type
         is kept local to expressions.  *)
      true
  | Sig_module (_, _, {md_type = mty}, _, _) ->
      contains_type env mty
  | Sig_value _
  | Sig_type _
  | Sig_typext _
  | Sig_class _
  | Sig_class_type _ ->
      false


(* Remove module aliases from a signature *)

let rec get_prefixes = function
  | Pident _ -> Path.Set.empty
  | Pdot (p, _)
  | Papply (p, _) -> Path.Set.add p (get_prefixes p)

let rec get_arg_paths = function
  | Pident _ -> Path.Set.empty
  | Pdot (p, _) -> get_arg_paths p
  | Papply (p1, p2) ->
      Path.Set.add p2
        (Path.Set.union (get_prefixes p2)
           (Path.Set.union (get_arg_paths p1) (get_arg_paths p2)))

let rec rollback_path subst p =
  try Pident (Path.Map.find p subst)
  with Not_found ->
    match p with
      Pident _ | Papply _ -> p
    | Pdot (p1, s) ->
        let p1' = rollback_path subst p1 in
        if Path.same p1 p1' then p else rollback_path subst (Pdot (p1', s))

let rec collect_ids subst bindings p =
    begin match rollback_path subst p with
      Pident id ->
        let ids =
          try collect_ids subst bindings (Ident.find_same id bindings)
          with Not_found -> Ident.Set.empty
        in
        Ident.Set.add id ids
    | _ -> Ident.Set.empty
    end

let collect_arg_paths mty =
  let open Btype in
  let paths = ref Path.Set.empty
  and subst = ref Path.Map.empty
  and bindings = ref Ident.empty in
  (* let rt = Ident.create "Root" in
     and prefix = ref (Path.Pident rt) in *)
  let it_path p = paths := Path.Set.union (get_arg_paths p) !paths
  and it_signature_item it si =
    type_iterators.it_signature_item it si;
    match si with
    | Sig_module (id, _, {md_type=Mty_alias p}, _, _) ->
        bindings := Ident.add id p !bindings
    | Sig_module (id, _, {md_type=Mty_signature sg}, _, _) ->
        Signature.iter
          (function Sig_module (id', _, _, _, _) ->
              subst :=
                Path.Map.add (Pdot (Pident id, Ident.name id')) id' !subst
            | _ -> ())
          sg
    | _ -> ()
  in
  let it = {type_iterators with it_path; it_signature_item} in
  it.it_module_type it mty;
  it.it_module_type unmark_iterators mty;
  Path.Set.fold (fun p -> Ident.Set.union (collect_ids !subst !bindings p))
    !paths Ident.Set.empty

type remove_alias_args =
    { mutable modified: bool;
      exclude: Ident.t -> Path.t -> bool;
      scrape: Env.t -> module_type -> module_type }

let rec remove_aliases_mty env args pres mty =
  let args' = {args with modified = false} in
  let res =
    match args.scrape env mty with
      Mty_signature sg ->
        Mp_present,
        Mty_signature (Signature.unpack sg |> remove_aliases_sig env args' |> Signature.pack)
    | Mty_alias _ ->
        let mty' = Env.scrape_alias env mty in
        if mty' = mty then begin
          pres, mty
        end else begin
          args'.modified <- true;
          remove_aliases_mty env args' Mp_present mty'
        end
    | mty ->
        Mp_present, mty
  in
  if args'.modified then begin
    args.modified <- true;
    res
  end else begin
    pres, mty
  end

and remove_aliases_sig env args sg =
  match sg with
    [] -> []
  | Sig_module(id, pres, md, rs, priv) :: rem  ->
      let pres, mty =
        match md.md_type with
          Mty_alias p when args.exclude id p ->
            pres, md.md_type
        | mty ->
            remove_aliases_mty env args pres mty
      in
      Sig_module(id, pres, {md with md_type = mty} , rs, priv) ::
      remove_aliases_sig (Env.add_module id pres mty env) args rem
  | Sig_modtype(id, mtd, priv) :: rem ->
      Sig_modtype(id, mtd, priv) ::
      remove_aliases_sig (Env.add_modtype id mtd env) args rem
  | it :: rem ->
      it :: remove_aliases_sig env args rem

let scrape_for_functor_arg env mty =
  let exclude _id p =
    try ignore (Env.find_module p env); true with Not_found -> false
  in
  let _, mty =
    remove_aliases_mty env {modified=false; exclude; scrape} Mp_present mty
  in
  mty

let scrape_for_type_of ~remove_aliases env mty =
  if remove_aliases then begin
    let excl = collect_arg_paths mty in
    let exclude id _p = Ident.Set.mem id excl in
    let scrape _ mty = mty in
    let _, mty =
      remove_aliases_mty env {modified=false; exclude; scrape} Mp_present mty
    in
    mty
  end else begin
    let _, mty = scrape_for_type_of env Mp_present mty in
    mty
  end

(* Lower non-generalizable type variables *)

let lower_nongen nglev mty =
  let open Btype in
  let it_type_expr it ty =
    match get_desc ty with
      Tvar _ ->
        let level = get_level ty in
        if level < generic_level && level > nglev then set_level ty nglev
    | _ ->
        type_iterators.it_type_expr it ty
  in
  let it = {type_iterators with it_type_expr} in
  it.it_module_type it mty;
  it.it_module_type unmark_iterators mty
