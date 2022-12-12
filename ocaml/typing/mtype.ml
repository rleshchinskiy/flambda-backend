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

let rl_debugging = Option.is_some (Sys.getenv_opt "RL_DEBUGGING")

let rl_with = Option.is_some (Sys.getenv_opt "RL_WITH")

(*
let rl_pr8548 = 
  let sfx p s =
    let m = String.length p in
    let n = String.length s in
    n >= m && String.sub s (n-m) m = p
  in
  Array.exists (sfx "pr8548.ml") Sys.argv
*)

let rl_expanding = ref false

let freshen ~scope mty =
  Subst.modtype (Rescope scope) Subst.identity mty

let rec strengthen_lazy ~aliasable env mty p =
  let open Subst.Lazy in
  match mty with
    MtyL_signature sg ->
      let _, sg = strengthen_lazy_sig ~aliasable env sg p in
      MtyL_signature sg
  | MtyL_functor(Named (Some param, arg), res)
    when !Clflags.applicative_functors ->
      let env =
        Env.add_module_lazy ~update_summary:false param Mp_present arg env
      in
      MtyL_functor(Named (Some param, arg),
        strengthen_lazy ~aliasable:false env res (Papply(p, Pident param)))
  | MtyL_functor(Named (None, arg), res)
    when !Clflags.applicative_functors ->
      let param = Ident.create_scoped ~scope:(Path.scope p) "Arg" in
      MtyL_functor(Named (Some param, arg),
        strengthen_lazy ~aliasable:false env res (Papply(p, Pident param)))
  | MtyL_ident (q, nom) ->
      begin match expand_lazy_nominal env q nom with
      | Some (MtyL_signature sg) ->
        let withs, sg = strengthen_lazy_sig ~aliasable env sg p in
        begin match withs with
        | Some cs when rl_with -> MtyL_ident (q, Nominal.add nom cs)
        | _ -> MtyL_signature sg
        end
      | Some mty -> strengthen_lazy ~aliasable env mty p
      | None -> mty (* RL: FIXME what about constraints? *)
      end
  | mty ->
      mty

and strengthen_lazy_sig' ~aliasable env sg p =
  let open Subst.Lazy in
  let add_with w = Option.map (fun ws -> w :: ws) in
  let strengthen_item (env, withs) = function
    | SigL_value(_, _, _) as sigelt ->
        ((env, withs), Some sigelt)
    | SigL_type(id, {type_kind=Type_abstract}, _, _)
      when Btype.is_row_name (Ident.name id) ->
        ((env, withs), None)
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
              (decl, add_with ([Ident.name id], Nominal.Modc_type name) withs )
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
        let constr = Nominal.Modc_module (Mtt_strengthen (Mtt_lookup, name, aliasable)) in
        let bind = ([Ident.name id], constr) in
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
              {decl with mtdl_type = Some(MtyL_ident(Pdot(p,Ident.name id), Nominal.empty))}
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
  let sg = Subst.Lazy.force_signature_once sg in
  let withs, sg = strengthen_lazy_sig' ~aliasable env sg p in
  withs, Subst.Lazy.of_signature_items sg

and strengthen_lazy_decl ~aliasable env md p =
  let open Subst.Lazy in
  let md' = match md.mdl_type with
  | MtyL_alias _ -> md
  | _ when aliasable -> {md with mdl_type = MtyL_alias p}
  | mty -> {md with mdl_type = strengthen_lazy ~aliasable env mty p}
  in
  if rl_debugging then (
    Format.printf "@[<hv 2>strengthen_lazy_decl %a@ %a@ %a@]@."
      Printtyp.path p
      Printtyp.modtype (force_modtype md.mdl_type)
      Printtyp.modtype (force_modtype md'.mdl_type)
  );
  md'

and constrain_modtype env constr mty =
  let open Subst.Lazy in
  match mty with
  | MtyL_ident (p, nom) ->
      MtyL_ident (p, Nominal.add nom [constr])
  | MtyL_alias p ->
      let p = Env.normalize_module_path (Some Location.none) env p in
      let mty = (Env.find_module_lazy p env).mdl_type in
      constrain_modtype env constr mty
  | MtyL_signature sg -> MtyL_signature (constrain_signature env constr sg)
  | MtyL_functor _ ->
      (* RL FIXME *)
      assert false

and constrain_signature env constr sg =
  Subst.Lazy.force_signature_once sg
  |> List.fold_left_map (constrain_sig_item constr) env
  |> snd
  |> Subst.Lazy.of_signature_items

and constrain_sig_item constr env item =
  let open Subst.Lazy in
  match constr, item with
  | ([s], Nominal.Modc_module t), SigL_module(id, pres, md, rs, vis)
    when Ident.name id = s ->
    let open Nominal in
    (*
      let md' = match md.mdl_type with
  | MtyL_alias _ -> md
  | _ when aliasable -> {md with mdl_type = MtyL_alias p}
  | mty -> {md with mdl_type = strengthen_lazy ~aliasable env mty p}
  *)
    let rec constrain = function
      | Mtt_lookup -> md.mdl_type
      | Mtt_exactly mty -> mty
      | Mtt_strengthen (t,p,a) ->
          begin match constrain t with
          | MtyL_alias _ as mty -> mty
          | _ when a -> MtyL_alias p
          | mty -> strengthen_lazy ~aliasable:a env mty p
          end
      | Mtt_dot (t,s) ->
        let pick s = function
          | (SigL_module(id, _, md, _, _)) when Ident.name id = s -> Some md.mdl_type
          | _ -> None
        in
        let project_item s = List.find_map (pick s) in
        let rec project = function
          | MtyL_alias p -> MtyL_alias (Path.Pdot (p,s))
          | MtyL_ident (p,nom) when Nominal.is_empty nom ->
              MtyL_ident (Path.Pdot (p,s), nom)
          | MtyL_ident (p,nom) ->
              begin match expand_lazy_nominal env p nom with
              | Some mty -> project mty
              | None -> assert false
              end
          | MtyL_functor _ -> assert false
          | MtyL_signature sg ->
              let items = Subst.Lazy.force_signature_once sg in
              begin match project_item s items with
              | Some mty -> mty
              | None -> assert false
              end
          in
          project (constrain t)
        | Mtt_apply (t,arg) ->
          let rec apply = function
          | MtyL_alias p -> MtyL_alias (Path.Papply (p,arg))
          | MtyL_ident (p,nom) when Nominal.is_empty nom ->
              MtyL_ident (Path.Papply(p,arg), nom)
          | MtyL_ident (p,nom) ->
              begin match expand_lazy_nominal env p nom with
              | Some mty -> apply mty
              | None -> assert false
              end
          | MtyL_functor (param, mty_res) ->
              begin match param with
              | Named (id, mty_param) ->
                let scope = Ctype.create_scope () in
                let subst = match id with
                  | None -> Subst.identity
                  | Some p ->
                      let mty_param = Subst.Lazy.force_modtype mty_param in
                      Subst.add_module_arg p arg mty_param Subst.identity
                in
                Subst.Lazy.modtype (Rescope scope) subst mty_res 
              | Unit -> assert false (* RL : FIXME *)
              end
          | MtyL_signature _ -> assert false
          in
          apply (constrain t)
    in
    let str = {md with mdl_type = constrain t}
    in
      (* RL FIXME: s/md/str/ *)
      let env =
        Env.add_module_declaration_lazy ~update_summary:false id pres md env in
      if rl_debugging then (
        Format.printf "@[<hv 2>constrain@ %a@ %a@]@."
          Printtyp.modtype (force_modtype md.mdl_type)
          Printtyp.modtype (force_modtype str.mdl_type)
      );
      env, SigL_module (id, pres, str, rs, vis)

  | ([s], Nominal.Modc_type p), SigL_type(id, decl, rs, vis) when Ident.name id = s ->
      let decl =
        match decl.type_manifest, decl.type_private, decl.type_kind with
          Some _, Public, _ -> decl
        | Some _, Private, (Type_record _ | Type_variant _) -> decl
        | _ ->
          if rl_debugging then (
            Format.printf "@[<hv 2>renaming %a to %a@]@."
              Printtyp.ident id
              Printtyp.path p
          );
          let manif = 
                Some(Btype.newgenty(Tconstr(p, decl.type_params, ref Mnil)))
          in
          if decl.type_kind = Type_abstract then
            { decl with type_private = Public; type_manifest = manif }
          else
            { decl with type_manifest = manif }
      in
      env, SigL_type(id, decl, rs, vis)

  | (s :: ns, c), SigL_module(id, pres, md, rs, vis) when Ident.name id = s ->
      let md = { md with mdl_type = constrain_modtype env (ns,c) md.mdl_type } in
      let env =
        Env.add_module_declaration_lazy ~update_summary:false id pres md env in
      env, SigL_module(id, pres, md, rs, vis)

    | _, SigL_module (id, pres, md, rs, vis) -> 
      let env =
        Env.add_module_declaration_lazy ~update_summary:false id pres md env in
      env, SigL_module(id, pres, md, rs, vis)

    | _, SigL_modtype(id, decl, vis) ->
      let env = Env.add_modtype_lazy ~update_summary:false id decl env in
      env, SigL_modtype(id, decl, vis)
        (* Need to add the module type in case it is manifest *)

    | _, sigelt -> env, sigelt


and expand_lazy_nominal env p nom =
  let debug = rl_debugging && not (Nominal.is_empty nom) && not !rl_expanding in
  if debug then (rl_expanding := true);
  if debug then (
    Format.printf "@[<hv 2>expanding %a@]@."
      Printtyp.nominal_type (p, Nominal.map Subst.Lazy.force_modtype nom)
  );
  let r =
    match Env.find_modtype_expansion_lazy p env with
    | mty -> 
        let mty = 
          match Nominal.constraints nom with
          | [] -> mty
          | cs -> 
              let scope = Ctype.create_scope () in
              let mty = Subst.Lazy.modtype (Subst.Rescope scope) Subst.identity mty in
              List.fold_left (fun t c -> constrain_modtype env c t) mty cs
        in
        Some mty
    | exception Not_found -> None
  in
  begin match r with
  | Some mty when debug ->
    Format.printf "@[<hv 2>expand@ %a@ %a@]@."
      Printtyp.modtype (Subst.Lazy.force_modtype (MtyL_ident (p,nom)))
      Printtyp.modtype (Subst.Lazy.force_modtype mty)
  | _ -> ()
  end;
  if debug then (rl_expanding := false);
  r

let strengthen ~aliasable env mty p =
  let mty' = strengthen_lazy ~aliasable env (Subst.Lazy.of_modtype mty) p in
  let mty'' = Subst.Lazy.force_modtype mty' in
  if rl_debugging then (
    Format.printf "@[<hv 1>strengthen %a@ %a@ %a@]@."
      Printtyp.path p
      Printtyp.modtype mty
      Printtyp.modtype mty''
  );
  mty''

let strengthen_decl ~aliasable env md p =
  let md' = strengthen_lazy_decl ~aliasable env
              (Subst.Lazy.of_module_decl md) p in
  let md'' = Subst.Lazy.force_module_decl md' in
  if rl_debugging then (
    Format.printf "@[<hv 1>strengthen_decl %a@ %a@ %a@]@."
      Printtyp.path p
      Printtyp.modtype md.md_type
      Printtyp.modtype md''.md_type
  );
    md''
  
  
  
let rec sig_make_manifest sg =
  match sg with
    [] -> []
  | (Sig_value _ | Sig_class _ | Sig_class_type _) as t :: rem ->
    t :: sig_make_manifest rem
  | Sig_type (id,decl,rs,vis) :: rem ->
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
    Sig_type(Ident.rename id, newdecl, rs, vis) :: sig_make_manifest rem
  | Sig_typext _ as sigelt :: rem ->
    sigelt :: sig_make_manifest rem
  | Sig_module(id, pres, md, rs, vis) :: rem ->
    let md =
      match md.md_type with
      | Mty_alias _ -> md
      | _ -> {md with md_type = Mty_alias (Pident id)}
    in
    Sig_module(Ident.rename id, pres, md, rs, vis) :: sig_make_manifest rem
  | Sig_modtype(id, decl, vis) :: rem ->
    let newdecl =
      {decl with mtd_type =
                   match decl.mtd_type with
                   | None -> Some (Mty_ident (Pident id, Nominal.empty))
                   | Some _ -> decl.mtd_type }
    in
    Sig_modtype(Ident.rename id, newdecl, vis) :: sig_make_manifest rem

let rec make_aliases_absent pres mty =
  let open Subst.Lazy in
  let signature sg =
    force_signature_once sg
    |> make_aliases_absent_sig
    |> of_signature_items
  in
  match mty with
  | MtyL_alias _ -> Mp_absent, mty
  | MtyL_signature sg ->
      pres, MtyL_signature (signature sg)
  | MtyL_functor(arg, res) ->
      let _, res = make_aliases_absent Mp_present res in
      pres, MtyL_functor(arg, res)
  | MtyL_ident (p,nom) ->
      let recurse mty =
        let _, mty = make_aliases_absent pres mty in mty
      in
      pres, MtyL_ident (p, Nominal.map recurse nom)

and make_aliases_absent_sig sg =
  let open Subst.Lazy in
  match sg with
    [] -> []
  | SigL_module(id, pres, md, rs, priv) :: rem ->
      let pres, mdl_type = make_aliases_absent pres md.mdl_type in
      let md = { md with mdl_type } in
      SigL_module(id, pres, md, rs, priv) :: make_aliases_absent_sig rem
  | sigelt :: rem ->
      sigelt :: make_aliases_absent_sig rem

let scrape_for_lazy_type_of env pres mty =
  let rec loop env path mty =
    match mty, path with
    | Subst.Lazy.MtyL_alias path, _ -> begin
        try
          let md = Env.find_module_lazy path env in
          loop env (Some path) md.mdl_type
        with Not_found -> mty
      end
    | mty, Some path ->
        strengthen_lazy ~aliasable:false env mty path
    | _ -> mty
  in
  make_aliases_absent pres (loop env None mty)

let scrape_for_type_of env pres mty =
  let pres, mty = scrape_for_lazy_type_of env pres (Subst.Lazy.of_modtype mty)
  in
  pres, Subst.Lazy.force_modtype mty


let expand_nominal env p nom =
  expand_lazy_nominal env p (Subst.Lazy.of_nominal nom)
  |> Option.map Subst.Lazy.force_modtype

let rec scrape_lazy env mty =
  let open Subst.Lazy in
  match mty with
    MtyL_ident (p, nom) ->
      begin match expand_lazy_nominal env p nom with
      | Some mty -> scrape_lazy env mty
      | None -> mty
      end
  | _ -> mty

let scrape env mty =
  match mty with
    Mty_ident (p, nom) when Nominal.is_empty nom ->
      Subst.Lazy.force_modtype (scrape_lazy env (MtyL_ident (p, Nominal.empty)))
  | _ -> mty


let () =
  Env.strengthen := strengthen_lazy ;
  Env.expand_lazy_nominal := expand_lazy_nominal ;
  Env.expand_nominal := expand_nominal


(* In nondep_supertype, env is only used for the type it assigns to id.
   Hence there is no need to keep env up-to-date by adding the bindings
   traversed. *)

type variance = Co | Contra | Strict

let rec nondep_mty_with_presence env va ids pres mty =
  match mty with
    Mty_ident (p, nom) ->
      begin match Path.find_free_opt ids p with
      | None when Nominal.is_empty nom -> pres, mty
      | r ->
        begin match expand_nominal env p nom with
        | Some expansion -> nondep_mty_with_presence env va ids pres expansion
        | None -> match r with
          | Some id -> raise (Ctype.Nondep_cannot_erase id)
          | None -> assert false (* RL: FIXME *)
        end
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
  List.map (nondep_sig_item env va ids) sg

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
    Mty_signature sg ->
      Mty_signature(List.map (enrich_item env p) sg)
  | Mty_ident (id,nom) when not (Nominal.is_empty nom) ->
      begin match expand_nominal env id nom with
      | Some mty -> enrich_modtype env p mty
      | None -> mty
      end
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
  match mty with
    Mty_ident (q,nom) ->
      begin match expand_nominal env q nom with
      | Some mty -> type_paths env p mty
      | None -> [] (* RL: FIXME I think this is ok? *)
      end
  | Mty_alias _ -> []
  | Mty_signature sg -> type_paths_sig env p sg
  | Mty_functor _ -> []

and type_paths_sig env p sg =
  match sg with
    [] -> []
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

and no_code_needed_sig env sg =
  match sg with
    [] -> true
  | Sig_value(_id, decl, _) :: rem ->
      begin match decl.val_kind with
      | Val_prim _ -> no_code_needed_sig env rem
      | _ -> false
      end
  | Sig_module(id, pres, md, _, _) :: rem ->
      no_code_needed_mod env pres md.md_type &&
      no_code_needed_sig
        (Env.add_module_declaration ~check:false id pres md env) rem
  | (Sig_type _ | Sig_modtype _ | Sig_class_type _) :: rem ->
      no_code_needed_sig env rem
  | (Sig_typext _ | Sig_class _) :: _ ->
      false

let no_code_needed env mty = no_code_needed_mod env Mp_present mty

(* Check whether a module type may return types *)

let rec contains_type env = function
    Mty_ident (path, nom) ->
      begin match expand_nominal env path nom with
        | Some mty -> contains_type env mty
        | None -> raise Exit (* PR#6427 *)
      end
  | Mty_signature sg ->
      contains_type_sig env sg
  | Mty_functor (_, body) ->
      contains_type env body
  | Mty_alias _ ->
      ()

and contains_type_sig env = List.iter (contains_type_item env)

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
      raise Exit
  | Sig_module (_, _, {md_type = mty}, _, _) ->
      contains_type env mty
  | Sig_value _
  | Sig_type _
  | Sig_typext _
  | Sig_class _
  | Sig_class_type _ ->
      ()

let contains_type env mty =
  try contains_type env mty; false with Exit -> true


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
    let module_type id = function
      | Mty_alias p ->
          bindings := Ident.add id p !bindings
      | Mty_signature sg ->
          List.iter
            (function Sig_module (id', _, _, _, _) ->
                subst :=
                  Path.Map.add (Pdot (Pident id, Ident.name id')) id' !subst
              | _ -> ())
            sg
      (* RL FIXME: This is probably very wrong for with constraints? *)
      | _ -> ()
    in
    match si with
    | Sig_module (id, _, {md_type=mty}, _, _) -> module_type id mty
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
        Mp_present, Mty_signature (remove_aliases_sig env args' sg)
    | Mty_ident (p,nom) ->
        Mp_present, Mty_ident (p, Nominal.map (
          fun mty -> remove_aliases_mty env args' pres mty |> snd) nom)
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
