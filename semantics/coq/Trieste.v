From TLC Require Import LibCore LibTactics LibWf LibList LibNat LibEnv.

Import LibListNotation.

Ltac auto_star ::= try solve [eauto with trieste | intuition eauto].

Local Hint Resolve Forall_last : trieste.
Local Hint Resolve Forall_nil : trieste.
Local Hint Constructors Forall : trieste.
Local Hint Resolve Forall_last_inv : trieste.

(*
Section MiniTrieste.
  Inductive pattern :=
  | PatNat: nat -> pattern
  | PatNot: pattern -> pattern
  | PatChoice: pattern -> pattern -> pattern.

  Inductive match_pattern: pattern -> nat -> option nat -> Prop :=
  | MatchNat:
    forall n,
      match_pattern (PatNat n) n (Some n)
  | NoMatchNat:
    forall n m,
      n <> m ->
      match_pattern (PatNat n) m None
  | MatchNot:
    forall p n,
      match_pattern p n None ->
      match_pattern (PatNot p) n (Some n)
  | NoMatchNot:
    forall p n,
      match_pattern p n (Some n) ->
      match_pattern (PatNot p) n None
  | MatchChoiceL:
    forall p1 p2 n,
      match_pattern p1 n (Some n) ->
      match_pattern (PatChoice p1 p2) n (Some n)
  | MatchChoiceR:
    forall p1 p2 n m,
      match_pattern p1 n None ->
      match_pattern p2 n (Some m) ->
      match_pattern (PatChoice p1 p2) n (Some m)
  | NoMatchChoice:
    forall p1 p2 n,
      match_pattern p1 n None ->
      match_pattern p2 n None ->
      match_pattern (PatChoice p1 p2) n None.

  Theorem nomatch_pattern_is_negation:
    forall p n m,
      match_pattern p n None ->
      ~match_pattern p n (Some m).
  Proof using.
    introv Hnmatch contra.
    induction p.
    - inverts Hnmatch. inverts* contra.
    - inverts Hnmatch. inverts* contra.
    - inverts Hnmatch. inverts* contra.
  Qed.

  Theorem match_pattern_is_deterministic:
    forall p n res1 res2,
      match_pattern p n res1 ->
      match_pattern p n res2 ->
      res1 = res2.
  Proof using.
    introv Hmatch1 Hmatch2.
    gen res2. induction Hmatch1; intros; inverts* Hmatch2.
    - forwards* contra: IHHmatch1.
    - forwards* contra: IHHmatch1.
    - forwards* contra: IHHmatch1. inverts contra.
    - forwards* contra: IHHmatch1_1. inverts contra.
  Qed.

End MiniTrieste.
*)

Section Trieste.
  Variable label : Type.
  Variables group top invalid unclosed : label.

  (* TODO: Position information for errors *)
  Inductive term :=
  | Tm : label -> list term -> term
  | Cursor : term
  | MStart : term
  | MEnd   : term.

  Notation Group := (Tm group).
  Notation Top := (Tm top).
  Notation Invalid := (Tm invalid []).
  Notation Unclosed := (Tm unclosed []).
  Notation new lbl := (Tm lbl nil).

  Notation "pre '|>' tms '<|' post" := (pre ++ MStart :: tms ++ MEnd :: post)%list (at level 400, right associativity).
  Notation "'|>' tms '<|' post" := (nil ++ MStart :: tms ++ MEnd :: post)%list (at level 400, right associativity).
  Notation "pre '|>' '<|' post" := (pre ++ MStart :: nil ++ MEnd :: post)%list (at level 400, right associativity).
  Notation "pre '|>' tms '<|'" := (pre ++ MStart :: tms ++ MEnd :: nil)%list (at level 400, right associativity).
  Notation "pre '|>' '<|'" := (pre ++ MStart :: nil ++ MEnd :: nil)%list (at level 400, right associativity).
  Notation "'|>' tms '<|'" := (nil ++ MStart :: tms ++ MEnd :: nil)%list (at level 400, right associativity).
  Notation "'|>' '<|' post" := (nil ++ MStart :: nil ++ MEnd :: post) (at level 400, right associativity).
  Notation "'|>' '<|'" := (nil ++ MStart :: nil ++ MEnd :: nil)%list (at level 400, right associativity).

  (* TODO: Different kinds of contexts? *)

  Fixpoint term_size(tm: term): nat :=
    match tm with
    | Tm _ tms =>
      let fix terms_size tms: nat :=
        match tms with
        | nil => 0
        | tm :: tms' => term_size tm + terms_size tms'
        end
      in
      1 + terms_size tms
    | _ => 1
    end.

  Fixpoint terms_size(tms: list term): nat :=
    match tms with
    | nil => 0
    | tm :: tms' => term_size tm + terms_size tms'
    end.
  Hint Unfold terms_size : trieste.

  Lemma term_size_positive:
    forall tm,
      term_size tm > 0.
  Proof using.
    introv. destruct tm; simpl; nat_math.
  Qed.

  Lemma term_size_last:
    forall lbl tms tm,
      term_size (Tm lbl (tms & tm)) =
        term_size (Tm lbl tms) + term_size tm.
  Proof using.
    introv. induction tms; rew_list; simpls; nat_math.
  Qed.

  Lemma term_size_app:
    forall lbl pre post,
      term_size (Tm lbl (pre ++ post)) =
        term_size (Tm lbl pre) + terms_size post.
  Proof using.
    introv. induction pre; rew_list; simpls*; nat_math.
  Qed.

  Lemma terms_size_last:
    forall tms tm,
      terms_size (tms & tm) = terms_size tms + term_size tm.
  Proof using.
    introv. inductions tms; rew_list; simpls*.
    rewrite IHtms. nat_math.
  Qed.

  Lemma terms_size_app:
    forall tms1 tms2,
      terms_size (tms1 ++ tms2) = terms_size tms1 + terms_size tms2.
  Proof using.
    introv. inductions tms1; rew_list; simpls*.
    rewrite IHtms1. nat_math.
  Qed.

  Ltac solve_IH :=
    try match goal with
    | _ : _ |- context[Tm _ (_ ++ _)] => rewrites term_size_app
    end;
    try match goal with
    | _ : _ |- context[Tm _ (_ & _)] => rewrites term_size_last
    end;
    try match goal with
    | _ : _ |- context[term_size ?tm + _] => forwards: term_size_positive tm
    end;
    simpls;
    nat_math.

  Hint Extern 0 =>
    match goal with
      _ : _ |- term_size _ < term_size _ => solve_IH
    end : trieste.

  Inductive is_term : term -> Prop :=
  | IsTermTm:
      forall lbl tms,
        Forall is_term tms ->
        is_term (Tm lbl tms).
  Hint Constructors is_term : trieste.

  Lemma is_term_last_inv:
    forall lbl tms tm,
      is_term (Tm lbl (tms & tm)) ->
      Forall is_term tms /\ is_term tm.
  Proof using.
    introv Htm. inverts* Htm.
  Qed.

  Inductive is_parsing_term : term -> Prop :=
  | IsPTermTm:
      forall lbl tms tm,
        Forall is_term tms ->
        is_parsing_term tm ->
        is_parsing_term (Tm lbl (tms & tm))
  | IsPTermCursor:
      is_parsing_term Cursor.
  Hint Constructors is_parsing_term : trieste.

  Lemma is_parsing_term_last_inv:
    forall lbl tms tm,
      is_parsing_term (Tm lbl (tms & tm)) ->
      Forall is_term tms /\ is_parsing_term tm.
  Proof using.
    introv Hptm. inverts Hptm.
    forwards* (-> & ->): last_eq_last_inv H0.
  Qed.

  Ltac is_parsing_term_inv :=
    repeat match goal with
      | H : is_parsing_term (Tm _ (_ & _)) |- _ =>
          forwards (? & ?): is_parsing_term_last_inv H; clear H
      | H : is_parsing_term (Group (_ & _)) |- _ =>
          forwards (? & ?): is_parsing_term_last_inv H; clear H
      | H : is_parsing_term (Top (_ & _)) |- _ =>
          forwards (? & ?): is_parsing_term_last_inv H; clear H
      end.

  Tactic Notation "is_parsing_term_inv" "*" := is_parsing_term_inv; auto_star.
  (* TODO: Should teach auto to try this when the goal is an is_parsing_term *)

  Inductive is_matching_term : term -> Prop :=
  | IsMTermLater:
    forall lbl pre tm post,
      Forall is_term pre ->
      Forall is_term post ->
      is_matching_term tm ->
      is_matching_term (Tm lbl (pre & tm ++ post))
  | IsMTermHere:
    forall lbl pre tms post,
      Forall is_term pre ->
      Forall is_term tms ->
      Forall is_term post ->
      is_matching_term (Tm lbl (pre |> tms <| post)).
  Hint Constructors is_matching_term : trieste.

  Lemma is_term_not_is_matching:
    forall tm,
      is_term tm ->
      ~is_matching_term tm.
  Proof using.
    intros tm. induction_wf IH: term_size tm. unfolds measure.
    introv Htm contra. inverts Htm as Hall. inverts contra.
    - forwards* (Hall' & _): Forall_app_inv. forwards* (_ & Htm): Forall_last_inv.
      applys* IH tm.
    - clear IH. induction pre.
      + rew_list in Hall. inverts Hall. inverts H4.
      + inverts Hall. inverts* H1.
  Qed.

  Fixpoint count_cursors(tm: term): nat :=
    match tm with
    | Tm _ tms =>
        let fix count_cursors_list tms : nat :=
          match tms with
          | nil => 0
          | tm :: tms' => count_cursors tm + count_cursors_list tms'
          end
        in
        count_cursors_list tms
    | Cursor => 1
    | _ => 0
    end.

  Lemma count_cursors_snoc:
    forall lbl tms tm,
      count_cursors (Tm lbl (tms & tm)) =
        count_cursors (Tm lbl tms) + count_cursors tm.
  Proof using.
    introv. induction tms; rew_list; simpls*.
    rewrites IHtms. nat_math.
  Qed.

  Example is_term_no_cursor:
    forall tm,
      is_term tm ->
      count_cursors tm = 0.
  Proof using.
    intros tm. induction_wf IH: term_size tm. unfolds measure.
    introv Htm. inverts Htm as Hall.
    induction* Hall.
    simpl. rewrites* IH.
  Qed.

  Example parsing_term_single_cursor:
    forall tm,
      is_parsing_term tm ->
      count_cursors tm = 1.
  Proof using.
    intros tm. induction_wf IH: term_size tm.
    unfolds measure. introv Hptm.
    inverts* Hptm. rewrite count_cursors_snoc.
    asserts* Htm: (is_term (Tm lbl tms)).
    rewrites* is_term_no_cursor.
  Qed.

(*********************************************)
(* Parsing                                   *)
(*********************************************)

  Inductive action :=
  | ActAdd      : label -> action
  | ActPush     : label -> action
  | ActPop      : label -> action
  | ActSeq      : label -> action
  | ActTerm     : list label -> action
  | ActTryPop   : label -> action
  | ActInvalid  : action
  | ActUnclosed : action
  | ActDone     : action.

  Inductive parse : action -> term -> term -> Prop :=
  | ParseCtx:
    forall lbl tms tm1 tm2 a,
      (forall lbls, a <> ActTerm lbls) ->
      a <> ActDone ->
      parse a tm1 tm2 ->
      parse a (Tm lbl (tms & tm1)) (Tm lbl (tms & tm2))
  | ParseAddIn:
    forall lbl tms,
      parse (ActAdd lbl)
            (Group (tms & Cursor))
            (Group (tms & new lbl & Cursor))
  | ParseAddCreate:
    forall lbl' lbl tms,
      lbl' <> group ->
      parse (ActAdd lbl)
            (Tm lbl' (tms & Cursor))
            (Tm lbl' (tms & (Group ([new lbl] & Cursor))))
  | ParsePushIn:
    forall lbl tms,
      parse (ActPush lbl)
            (Group (tms & Cursor))
            (Group (tms & Tm lbl [Cursor]))
  | ParsePushCreate:
    forall lbl lbl' tms,
      lbl' <> group ->
      parse (ActPush lbl)
            (Tm lbl' (tms & Cursor))
            (Tm lbl' (tms & Group [Tm lbl [Cursor]]))
  | ParsePopOK:
    forall lbl lbl' tms tms' tm,
      parse (ActTryPop lbl)
            (Tm lbl' (tms & Tm lbl (tms' & Cursor)))
            tm ->
      parse (ActPop lbl)
            (Tm lbl' (tms & Tm lbl (tms' & Cursor)))
            tm
  | ParsePopFail:
    forall lbl lbl' lbl'' tms tms' tm,
      lbl'' <> lbl ->
      parse (ActInvalid)
            (Tm lbl'' (tms' & Cursor))
            tm ->
      parse (ActPop lbl)
            (Tm lbl' (tms & Tm lbl'' (tms' & Cursor)))
            (Tm lbl' (tms & tm))
  | ParseTryPopOK:
    forall lbl lbl' tms tms',
      parse (ActTryPop lbl)
            (Tm lbl' (tms & Tm lbl (tms' & Cursor)))
            (Tm lbl' (tms & Tm lbl tms' & Cursor))
  | ParseTryPopFail:
    forall lbl lbl' lbl'' tms tms',
      lbl'' <> lbl ->
      parse (ActTryPop lbl)
            (Tm lbl' (tms & Tm lbl'' (tms' & Cursor)))
            (Tm lbl' (tms & Tm lbl'' (tms' & Cursor)))
  | ParseInvalidExtend:
    forall lbl tms,
      parse ActInvalid
            (Tm lbl (tms & Invalid & Cursor))
            (Tm lbl (tms & Invalid & Cursor))
  | ParseInvalidEmpty:
    forall lbl tm,
      parse (ActAdd invalid)
            (Tm lbl (nil & Cursor))
            tm ->
      parse ActInvalid
            (Tm lbl (nil & Cursor))
            tm
  | ParseInvalidNonEmpty:
    forall lbl lbl' tms tms' tm,
      lbl' <> invalid ->
      parse (ActAdd invalid)
            (Tm lbl (tms & Tm lbl' tms' & Cursor))
            tm ->
      parse ActInvalid
            (Tm lbl (tms & Tm lbl' tms' & Cursor))
            tm
  | ParseSeqIn:
    forall lbl tms tms',
      parse (ActSeq lbl)
            (Tm lbl (tms & Group (tms' & Cursor)))
            (Tm lbl (tms & Group tms' & Cursor))
  | ParseSeqCreate:
    forall lbl lbl' tms tms',
      lbl' <> lbl ->
      parse (ActSeq lbl)
            (Tm lbl' (tms & Group (tms' & Cursor)))
            (Tm lbl' (tms & Tm lbl ([Group tms'] & Cursor)))
  | ParseSeqFail:
    forall lbl lbl' tms tm,
      lbl' <> group ->
      parse ActInvalid
            (Tm lbl' (tms & Cursor))
            tm ->
      parse (ActSeq lbl)
            (Tm lbl' (tms & Cursor))
            tm
  | ParseTerm:
    forall lbls tm tm0 tmn ,
      parse (ActTryPop group) tm tm0 ->
      parse_trypop_many lbls tm0 tmn ->
      parse (ActTerm lbls) tm tmn
  | ParseDone:
    forall tms,
      parse (ActDone) (Top (tms & Cursor)) (Top tms)
  | ParseDoneGroup:
    forall tms tms',
      parse (ActDone) (Top (tms & (Group (tms' & Cursor)))) (Top (tms & Group tms'))
  (* Error handling *)
  | ParseDoneUnclosed:
    forall lbl tms tms' tm,
      lbl <> group ->
      is_term tm ->
      parse ActUnclosed (Top (tms & Tm lbl tms')) tm ->
      parse ActDone (Top (tms & Tm lbl tms')) tm
  | ParseUnclosedTop:
    forall tms,
      parse ActUnclosed (Top (tms & Cursor)) (Top (tms & Unclosed))
  | ParseUnclosedStep:
    forall tm tm' tmDone,
      is_term tmDone ->
      parse ActUnclosed tm tm' ->
      parse ActUnclosed tm' tmDone ->
      parse ActUnclosed tm tmDone
  | ParseUnclosedAdd:
    forall lbl lbl' tms tms',
      parse ActUnclosed
            (Tm lbl (tms & Tm lbl' (tms' & Cursor)))
            (Tm lbl (tms & Tm lbl' (tms' & Unclosed) & Cursor))
  | ParseUnclosedGroup:
    forall lbl lbl' tms tms' tms'',
      parse ActUnclosed
            (Tm lbl (tms & Tm lbl' (tms' & Group (tms'' & Cursor))))
            (Tm lbl (tms & Tm lbl' (tms' & Group tms'' & Unclosed) & Cursor))
  with
    parse_trypop_many : list label -> term -> term -> Prop :=
    | PopManyNil:
      forall tm,
        parse_trypop_many nil tm tm
    | PopManyCons:
      forall lbl lbls tmi tmi' tmn,
        parse (ActTryPop lbl) tmi tmi' ->
        parse_trypop_many lbls tmi' tmn ->
        parse_trypop_many (lbl :: lbls) tmi tmn.

  Lemma is_term_no_parse:
    forall tm tm' a,
      is_term tm ->
      ~parse a tm tm'.
  Proof using.
    intros tm. induction_wf IH: term_size tm.
    unfolds measure.
    introv Htm contra. induction* contra;
      try forwards (Hall & Htm'): is_term_last_inv Htm;
      try forwards (Hall' & Htm''): is_term_last_inv Htm';
      try solve [inverts Htm'
                |inverts Htm''].
    - applys* IH. solve_IH.
    - forwards (Hall'' & Htm'''): is_term_last_inv Htm''.
      inverts Htm'''.
  Qed.

  Lemma parse_cursor_inv:
    forall a tm,
      ~parse a Cursor tm.
  Proof using.
    intros a tm. induction_wf IH: term_size tm.
    introv contra. inverts contra.
    - inverts H.
    - inverts H0.
      applys* is_term_no_parse.
  Qed.

  Lemma parse_trypop_eq_inv:
    forall lbl lbl' tms tms' tm,
      parse (ActTryPop lbl) (Tm lbl' (tms & Tm lbl (tms' & Cursor))) tm ->
      tm = Tm lbl' (tms & Tm lbl tms' & Cursor).
  Proof using.
    introv Hparse.
    inverts Hparse.
    - forwards (-> & ->): last_eq_last_inv H0.
      inverts H5.
      + forwards (-> & ->): last_eq_last_inv H2.
        false* parse_cursor_inv.
      + forwards (-> & Heq): last_eq_last_inv H6.
        inverts Heq.
      + forwards (-> & Heq): last_eq_last_inv H6.
        inverts Heq.
    - forwards (-> & Heq): last_eq_last_inv H2.
      inverts Heq.
      forwards* (-> & Heq): last_eq_last_inv H0.
    - forwards (-> & Heq): last_eq_last_inv H2.
      inverts* Heq.
  Qed.

  Lemma parse_trypop_neq_inv:
    forall lbl lbl' lbl'' tms tms' tm,
      lbl'' <> lbl ->
      parse (ActTryPop lbl) (Tm lbl' (tms & Tm lbl'' (tms' & Cursor))) tm ->
      tm = Tm lbl' (tms & Tm lbl'' (tms' & Cursor)).
  Proof using.
    introv Hneq Hparse.
    inverts* Hparse.
    - forwards (-> & ->): last_eq_last_inv H0.
      inverts H5.
      + forwards (-> & ->): last_eq_last_inv H2.
        false* parse_cursor_inv.
      + forwards (-> & Heq): last_eq_last_inv H6.
        inverts Heq.
      + forwards (-> & Heq): last_eq_last_inv H6.
        inverts Heq.
    - forwards (-> & Heq): last_eq_last_inv H2.
      inverts* Heq.
  Qed.

  Lemma parse_trypop_preserves_cursor:
    forall lbl tm tm',
      is_parsing_term tm ->
      parse (ActTryPop lbl) tm tm' ->
      is_parsing_term tm'.
  Proof using.
    intros lbl tm. induction_wf IH: term_size tm.
    unfolds measure. introv Hptm Hparse.
    inverts* Hparse.
    - is_parsing_term_inv.
      forwards*: IH H3.
    - is_parsing_term_inv*.
  Qed.

  Lemma parse_trypop_many_preserves_cursor:
    forall lbls tm tm',
      is_parsing_term tm ->
      parse_trypop_many lbls tm tm' ->
      is_parsing_term tm'.
  Proof using.
    introv Hparse Htrypop.
    inductions lbls; inverts* Htrypop.
    forwards*: parse_trypop_preserves_cursor H1.
  Qed.

  Lemma parse_add_invalid_preserves_cursor:
    forall lbl tms tm',
      is_parsing_term (Tm lbl (tms & Cursor)) ->
      parse (ActAdd invalid) (Tm lbl (tms & Cursor)) tm' ->
      is_parsing_term tm'.
  Proof using.
    introv Hptm Hparse.
    forwards* (Hall & Htm): is_parsing_term_last_inv Hptm.
    inverts Hparse.
    - forwards (-> & ->): last_eq_last_inv H0.
      false* parse_cursor_inv.
    - forwards* (-> & _): last_eq_last_inv H2.
    - forwards* (-> & _): last_eq_last_inv H2.
  Qed.

  Lemma parse_invalid_preserves_cursor:
    forall lbl tms tm',
      is_parsing_term (Tm lbl (tms & Cursor)) ->
      parse (ActInvalid) (Tm lbl (tms & Cursor)) tm' ->
      is_parsing_term tm'.
  Proof using.
    introv Hptm Hparse.
    is_parsing_term_inv.
    inverts Hparse.
    - forwards (-> & ->): last_eq_last_inv H2.
      false* parse_cursor_inv.
    - forwards* (-> & _): last_eq_last_inv H3.
    - forwards* (<- & _): last_eq_last_inv H2.
      applys* parse_add_invalid_preserves_cursor.
    - forwards* (<- & _): last_eq_last_inv H2.
      applys* parse_add_invalid_preserves_cursor.
  Qed.

  Hint Extern 0 =>
         match goal with
         | _ : _ |- context[Tm _ [?tm]] => replaces [tm] with (nil & tm); [rew_list*|]
         end : trieste.

  Hint Extern 2 =>
         match goal with
         | H : parse ActInvalid _ ?tm |- is_parsing_term ?tm => applys parse_invalid_preserves_cursor
         | H : parse (ActAdd invalid) _ ?tm |- is_parsing_term ?tm => applys parse_add_invalid_preserves_cursor
         end : trieste.

  Lemma parse_preserves_cursor:
    forall a tm tm',
      a <> ActDone ->
      a <> ActUnclosed ->
      is_parsing_term tm ->
      parse a tm tm' ->
      is_parsing_term tm'.
  Proof using.
    intros a tm. induction_wf IH: term_size tm.
    unfolds measure. introv Hndone Hnunclosed Hptm Hparse.
    inverts Hparse;
      is_parsing_term_inv*.
    - forwards*: IH H3.
    - replaces [Cursor] with (nil & Cursor)%list; autos*.
    - replaces [Tm lbl [Cursor]] with (nil & Tm lbl (nil & Cursor))%list; autos*.
    - applys* parse_trypop_preserves_cursor (Tm lbl' (tms & Tm lbl (tms' & Cursor))).
    - forwards*: parse_trypop_preserves_cursor.
      applys* parse_trypop_many_preserves_cursor.
  Qed.

  Lemma parse_done_closes_term:
    forall tm tm',
      is_parsing_term tm ->
      parse ActDone tm tm' ->
      is_term tm'.
  Proof using.
    intros tm. induction_wf IH: term_size tm.
    introv Hptm Hparse. inverts* Hparse;
      is_parsing_term_inv*.
  Qed.

(*********************************************)
(* Matching                                  *)
(*********************************************)

  Inductive pattern : Type :=
  | PatFB  : pattern -> pattern
  | PatNFB : pattern -> pattern
  | PatIn  : label -> pattern
  | PatStart : pattern
  | PatEnd : pattern
  | PatLabel : label -> pattern
  | PatAny : pattern
  | PatChoice : pattern -> pattern -> pattern
  | PatSeq : pattern -> pattern -> pattern
  | PatChildren : pattern -> pattern -> pattern
  | PatNeg : pattern -> pattern
  | PatOption : pattern -> pattern
  | PatMany : pattern -> pattern
  | PatBind : pattern -> var -> pattern
  | PatAction : pattern -> (list term -> bool) -> pattern.

  Inductive is_predicate : pattern -> Prop :=
  | PredFB : forall p, is_predicate (PatFB p)
  | PredNFB : forall p, is_predicate (PatNFB p)
  | PredIn : forall p, is_predicate (PatIn p)
  | PredStart : is_predicate PatStart
  | PredEnd : is_predicate PatEnd.
  Hint Constructors is_predicate : trieste.

  Inductive multiplicity : Type :=
  | MulZero
  | MulOne
  | MulMany.

  Definition nat_to_multiplicity (n : nat) :=
    match n with
    | 0 => MulZero
    | 1 => MulOne
    | _ => MulMany
    end.

  Coercion nat_to_multiplicity : nat >-> multiplicity.
  Notation omega := (MulMany).

  Definition m_add (m1 m2 : multiplicity): multiplicity :=
    match m1, m2 with
    | MulZero, MulZero => 0
    | MulZero, MulOne
      | MulOne, MulZero => 1
    | _, _ => omega
    end.
  Notation "m1 '+' m2" := (m_add m1 m2).

  Definition m_mul (m1 m2 : multiplicity): multiplicity :=
    match m1, m2 with
    | MulZero, _
      | _, MulZero => 0
    | MulOne, m
      | m, MulOne => m
    | _, _ => omega
    end.
  Notation "m1 '*' m2" := (m_mul m1 m2).

  Definition m_choice (m1 m2 : multiplicity): multiplicity :=
    match m1, m2 with
    | MulZero, MulZero => 0
    | MulOne, MulOne => 1
    | _, _ => omega
    end.
  Notation "m1 '/' m2" := (m_choice m1 m2).

  Inductive has_multiplicity : multiplicity -> list term -> Prop :=
  | HasMultZero:
      has_multiplicity 0 nil
  | HasMultOne:
    forall tm,
      has_multiplicity 1 [tm]
  | HasMultOmega:
    forall tms,
      has_multiplicity omega tms.

  Definition env := env multiplicity.

  Fixpoint env_combine (op: multiplicity -> multiplicity -> multiplicity)
                       (d: multiplicity) (env1 env2: env): env :=
    match env1 with
    | (x, m1)::env1' =>
        match get x env2 with
        | Some m2 =>
            let env2' := filter (fun tup: var * multiplicity => let (y, _) := tup in x <> y) env2 in
            (x, op m1 m2)::env_combine op d env1' env2'
        | _ =>
            (x, op d m1)::env_combine op d env1' env2
        end
    | _ =>
        map (op d) env2
    end.
  (* TODO: Lemmas about env_combine *)

  Inductive wf_pattern : env -> pattern -> multiplicity -> Prop :=
  | WfFB:
    forall Gamma p m,
      wf_pattern Gamma p m ->
      wf_pattern empty (PatFB p) 0
  | WfNFB:
    forall Gamma p m,
      wf_pattern Gamma p m ->
      wf_pattern empty (PatNFB p) 0
  | WfIn:
    forall lbl,
      wf_pattern empty (PatIn lbl) 0
  | WfStart:
      wf_pattern empty PatStart 0
  | WfEnd:
      wf_pattern empty PatEnd 0
  | WfLbl:
    forall lbl,
      wf_pattern empty (PatLabel lbl) 1
  | WfAny:
      wf_pattern empty PatAny 1
  | WfChoice:
    forall env1 env2 p1 p2 m1 m2,
      wf_pattern env1 p1 m1 ->
      wf_pattern env2 p2 m2 ->
      wf_pattern (env_combine m_choice omega env1 env2) (PatChildren p1 p2) (m_choice m1 m2)
  | WfSeq:
    forall env1 env2 p1 p2 m1 m2,
      wf_pattern env1 p1 m1 ->
      wf_pattern env2 p2 m2 ->
      disjoint (dom env1) (dom env2) ->
      wf_pattern (env1 & env2) (PatSeq p1 p2) (m1 + m2)
  | WfChildren:
    forall env1 env2 p1 p2 m,
      wf_pattern env1 p1 1 ->
      wf_pattern env2 p2 m ->
      disjoint (dom env1) (dom env2) ->
      wf_pattern (env1 & env2) (PatChildren p1 p2) 1
  | WfOption:
    forall env p m,
      wf_pattern env p m ->
      wf_pattern (map (m_add omega) env) (PatOption p) omega
  | WfMany:
    forall env p m,
      wf_pattern env p m ->
      wf_pattern (map (m_add omega) env) (PatMany p) omega
  | WfNot:
    forall env p,
      wf_pattern env p 1 ->
      wf_pattern empty (PatNeg p) 1
  | WfBind:
    forall env p m x,
      wf_pattern env p m ->
      x # env ->
      wf_pattern (env & x ~ m) (PatBind p x) m
  | WfAction:
    forall env p m f,
      wf_pattern env p m ->
      wf_pattern env (PatAction p f) m.

  Definition bindings := LibEnv.env (list term).

  Inductive match_pattern : pattern -> term -> term -> bindings -> Prop :=
  | MatchCtx:
    forall p pi pre tm1 tm2 post M,
      (* TODO: I would rather not have the Foralls here *)
      Forall is_term pre ->
      Forall is_term post ->
      match_pattern p tm1 tm2 M ->
      match_pattern p (Tm pi (pre & tm1 ++ post))
                      (Tm pi (pre & tm2 ++ post)) M
  | MatchBind:
    forall p pi pre tms tms' post post' x M,
      match_pattern p (Tm pi (pre |> tms <| post))
                      (Tm pi (pre |> tms ++ tms' <| post')) M ->
      match_pattern (PatBind p x)
                    (Tm pi (pre |> tms <| post))
                    (Tm pi (pre |> tms ++ tms' <| post')) (M & x ~ tms')
  | MatchStart:
    forall pi post,
      match_pattern PatStart
                    (Tm pi (|> <| post))
                    (Tm pi (|> <| post)) empty
  | MatchEnd:
    forall pi pre,
      match_pattern PatEnd
                    (Tm pi (pre |> <|))
                    (Tm pi (pre |> <|)) empty
  | MatchIn:
      forall pi pre tms post,
        match_pattern (PatIn pi) (Tm pi (pre |> tms <| post))
                                 (Tm pi (pre |> tms <| post)) empty
  | MatchFB:
      forall p pi pre tms post tm M,
        match_pattern p (Tm pi (pre |> tms <| post)) tm M ->
        match_pattern (PatFB p) (Tm pi (pre |> tms <| post))
                                (Tm pi (pre |> tms <| post)) empty
  | MatchNFB:
      forall p pi pre tms post,
        nomatch_pattern p (Tm pi (pre |> tms <| post)) ->
        match_pattern (PatNFB p) (Tm pi (pre |> tms <| post))
                                 (Tm pi (pre |> tms <| post)) empty
  | MatchLabel:
      forall lbl pi pre tms tms' post,
        match_pattern (PatLabel lbl) (Tm pi (pre |> tms <| Tm lbl tms' :: post))
                                     (Tm pi (pre |> tms & Tm lbl tms' <| post)) empty
  | MatchAny:
      forall pi pre tms post tm,
        match_pattern (PatAny) (Tm pi (pre |> tms <| tm :: post))
                               (Tm pi (pre |> tms & tm <| post)) empty
  | MatchChoiceL:
    forall p1 p2 pi pre tms post tm M,
      match_pattern p1 (Tm pi (pre |> tms <| post)) tm M ->
      match_pattern (PatChoice p1 p2) (Tm pi (pre |> tms <| post)) tm M
  | MatchChoiceR:
    forall p1 p2 pi pre tms post tm M,
      nomatch_pattern p1 (Tm pi (pre |> tms <| post)) ->
      match_pattern p2 (Tm pi (pre |> tms <| post)) tm M ->
      match_pattern (PatChoice p1 p2) (Tm pi (pre |> tms <| post)) tm M
  | MatchSeq:
    forall p1 p2 pi pre tms post tm1 tm2 M1 M2,
      match_pattern p1 (Tm pi (pre |> tms <| post)) tm1 M1 ->
      match_pattern p2 tm1 tm2 M2 ->
      match_pattern (PatSeq p1 p2) (Tm pi (pre |> tms <| post)) tm2 (M1 & M2)
  | MatchChildren:
    forall p1 p2 pi pre tms tms' post lbl tm M1 M2,
      match_pattern p1 (Tm pi (pre |> tms <| Tm lbl tms' :: post))
                       (Tm pi (pre |> tms & Tm lbl tms' <| post)) M1 ->
      match_pattern p2 (Tm lbl (|> <| tms')) tm M2 ->
      match_pattern (PatChildren p1 p2)
                    (Tm pi (pre |> tms <| Tm lbl tms' :: post))
                    (Tm pi (pre |> tms & Tm lbl tms' <| post)) (M1 & M2)
  | MatchNot:
    forall p pi pre tms post tm,
      nomatch_pattern p (Tm pi (pre |> tms <| tm :: post)) ->
      match_pattern (PatNeg p) (Tm pi (pre |> tms <| tm :: post))
                               (Tm pi (pre |> tms & tm <| post)) empty
  | MatchOptionYes:
    forall p pi pre tms post tm M,
      match_pattern p (Tm pi (pre |> tms <| post)) tm M ->
      match_pattern (PatOption p) (Tm pi (pre |> tms <| post))
                                  tm M
  | MatchOptionNo:
    forall p pi pre tms post,
      nomatch_pattern p (Tm pi (pre |> tms <| post)) ->
      match_pattern (PatOption p) (Tm pi (pre |> tms <| post))
                                  (Tm pi (pre |> tms <| post)) empty
  | MatchManyMore:
    forall p pi pre tms tms' post post' tm M1 M2,
      match_pattern p (Tm pi (pre |> tms <| post))
                      (Tm pi (pre |> tms ++ tms' <| post')) M1 ->
      tms' <> nil ->
      match_pattern (PatMany p) (Tm pi (pre |> tms ++ tms' <| post')) tm M2 ->
      match_pattern (PatMany p) (Tm pi (pre |> tms <| post)) tm (M1 & M2)
  | MatchManyDone:
    forall p pi pre tms post,
      nomatch_pattern p (Tm pi (pre |> tms <| post)) ->
      match_pattern (PatMany p) (Tm pi (pre |> tms <| post))
                                (Tm pi (pre |> tms <| post)) empty
  | MatchAction:
    forall p f pi pre tms tms' post post' M,
      match_pattern p (Tm pi (pre |> tms <| post))
                      (Tm pi (pre |> tms ++ tms' <| post')) M ->
      f tms' = true ->
      match_pattern (PatAction p f) (Tm pi (pre |> tms <| post))
                                    (Tm pi (pre |> tms ++ tms' <| post')) M
  with
    nomatch_pattern : pattern -> term -> Prop :=
    (* TODO: Generalize? *)
    | NoMatchBind:
      forall p pi pre tms post x,
        nomatch_pattern p (Tm pi (pre |> tms <| post)) ->
        nomatch_pattern (PatBind p x) (Tm pi (pre |> tms <| post))
    | NoMatchStart:
      forall pi pre tms post,
        pre ++ tms <> nil ->
        nomatch_pattern PatStart (Tm pi (pre |> tms <| post))
    | NoMatchEnd:
      forall pi pre tms post,
        tms ++ post <> nil ->
        nomatch_pattern PatEnd (Tm pi (pre |> tms <| post))
    | NoMatchIn:
      forall lbl pi pre tms post,
        lbl <> pi ->
        nomatch_pattern (PatIn lbl) (Tm pi (pre |> tms <| post))
    | NoMatchFB:
      forall p pi pre tms post,
        nomatch_pattern p (Tm pi (pre |> tms <| post)) ->
        nomatch_pattern (PatFB p) (Tm pi (pre |> tms <| post))
    | NoMatchNFB:
      forall p pi pre tms post tm M,
        match_pattern p (Tm pi (pre |> tms <| post)) tm M ->
        nomatch_pattern (PatNFB p) (Tm pi (pre |> tms <| post))
    | NoMatchLabel:
      forall lbl lbl' pi pre tms tms' post,
        lbl <> lbl' ->
        nomatch_pattern (PatLabel lbl) (Tm pi (pre |> tms <| Tm lbl' tms' :: post))
    | NoMatchAny:
      forall pi pre tms,
        nomatch_pattern (PatAny) (Tm pi (pre |> tms <|))
    | NoMatchChoice:
      forall p1 p2 pi pre tms post,
        nomatch_pattern p1 (Tm pi (pre |> tms <| post)) ->
        nomatch_pattern p2 (Tm pi (pre |> tms <| post)) ->
        nomatch_pattern (PatChoice p1 p2) (Tm pi (pre |> tms <| post))
    | NoMatchSeqL:
      forall p1 p2 pi pre tms post,
        nomatch_pattern p1 (Tm pi (pre |> tms <| post)) ->
        nomatch_pattern (PatSeq p1 p2) (Tm pi (pre |> tms <| post))
    | NoMatchSeqR:
      forall p1 p2 pi pre tms post tm1 M1,
        match_pattern p1 (Tm pi (pre |> tms <| post)) tm1 M1 ->
        nomatch_pattern p2 tm1 ->
        nomatch_pattern (PatSeq p1 p2) (Tm pi (pre |> tms <| post))
    | NoMatchChildrenL:
      forall p1 p2 pi pre tms post,
        nomatch_pattern p1 (Tm pi (pre |> tms <| post)) ->
        nomatch_pattern (PatChildren p1 p2) (Tm pi (pre |> tms <| post))
    | NoMatchChildrenL2:
      forall p1 p2 pi pre tms tms' post post' M,
        match_pattern p1 (Tm pi (pre |> tms <| post))
                         (Tm pi (pre |> tms ++ tms' <| post')) M ->
        length tms' <> 1 ->
        nomatch_pattern (PatChildren p1 p2) (Tm pi (pre |> tms <| post))
    | NoMatchChildrenR:
      forall p1 p2 pi pre tms tms' post lbl M,
        match_pattern p1 (Tm pi (pre |> tms <| Tm lbl tms' :: post))
                         (Tm pi (pre |> tms & Tm lbl tms' <| post)) M ->
        nomatch_pattern p2 (Tm lbl (|> <| tms')) ->
        nomatch_pattern (PatChildren p1 p2) (Tm pi (pre |> tms <| Tm lbl tms' :: post))
    | NoMatchNot:
      forall p pi pre tms post tm M,
        match_pattern p (Tm pi (pre |> tms <| tm :: post))
                        (Tm pi (pre |> tms & tm <| post)) M ->
        nomatch_pattern (PatNeg p) (Tm pi (pre |> tms <| tm :: post))
    | NoMatchAction:
      forall p pi pre tms post f,
        nomatch_pattern p (Tm pi (pre |> tms <| post)) ->
        nomatch_pattern (PatAction p f) (Tm pi (pre |> tms <| post))
    | NoMatchActionFun:
      forall p pi pre tms tms' post post' M f,
        match_pattern p (Tm pi (pre |> tms <| post))
                        (Tm pi (pre |> tms ++ tms' <| post')) M ->
        f tms' = false ->
        nomatch_pattern (PatAction p f) (Tm pi (pre |> tms <| post)).

  Scheme match_pattern_mut := Induction for match_pattern Sort Prop
    with nomatch_pattern_mut := Induction for nomatch_pattern Sort Prop.

  Inductive match_pattern' : pattern -> term -> option (term * bindings) -> Prop :=
  | MatchCtx':
    forall p pi pre tm1 tm2 post M,
      (* TODO: I would rather not have the Foralls here *)
      Forall is_term pre ->
      Forall is_term post ->
      match_pattern' p tm1 (Some (tm2, M)) ->
      match_pattern' p (Tm pi (pre & tm1 ++ post))
                 (Some (Tm pi (pre & tm2 ++ post), M))
  | NoMatchCtx':
    forall p pi pre tm post,
      (* TODO: I would rather not have the Foralls here *)
      Forall is_term pre ->
      Forall is_term post ->
      match_pattern' p tm None ->
      match_pattern' p (Tm pi (pre & tm ++ post))
                       None
  | MatchBind':
    forall p pi pre tms tms' post post' x M,
      match_pattern' p (Tm pi (pre |> tms <| post))
                 (Some (Tm pi (pre |> tms ++ tms' <| post'), M)) ->
      match_pattern' (PatBind p x)
                     (Tm pi (pre |> tms <| post))
               (Some (Tm pi (pre |> tms ++ tms' <| post'), M & x ~ tms'))
  | NoMatchBind':
    forall p pi pre tms post x,
      match_pattern' p (Tm pi (pre |> tms <| post)) None ->
      match_pattern' (PatBind p x)
                     (Tm pi (pre |> tms <| post)) None
  | MatchStart':
    forall pi post,
      match_pattern' PatStart
                     (Tm pi (|> <| post))
               (Some (Tm pi (|> <| post), empty))
  | NoMatchStart':
    forall pi pre tms post,
      pre ++ tms <> nil ->
      match_pattern' PatStart
                     (Tm pi (pre |> tms <| post)) None
  | MatchEnd':
    forall pi pre,
      match_pattern' PatEnd
                     (Tm pi (pre |> <|))
               (Some (Tm pi (pre |> <|), empty))
  | NoMatchEnd':
    forall pi pre tms post,
      tms ++ post <> nil ->
      match_pattern' PatEnd
                     (Tm pi (pre |> tms <| post)) None
  | MatchIn':
      forall pi pre tms post,
        match_pattern' (PatIn pi)
                       (Tm pi (pre |> tms <| post))
                 (Some (Tm pi (pre |> tms <| post), empty))
  | NoMatchIn':
      forall pi lbl pre tms post,
        lbl <> pi ->
        match_pattern' (PatIn lbl) (Tm pi (pre |> tms <| post)) None
  | MatchFB':
      forall p pi pre tms post tm M,
        match_pattern' p (Tm pi (pre |> tms <| post)) (Some (tm, M)) ->
        match_pattern' (PatFB p)
                       (Tm pi (pre |> tms <| post))
                 (Some (Tm pi (pre |> tms <| post), empty))
  | NoMatchFB':
      forall p pi pre tms post,
        match_pattern' p (Tm pi (pre |> tms <| post)) None ->
        match_pattern' (PatFB p)
                       (Tm pi (pre |> tms <| post)) None
  | MatchNFB':
      forall p pi pre tms post,
        match_pattern' p (Tm pi (pre |> tms <| post)) None ->
        match_pattern' (PatNFB p) (Tm pi (pre |> tms <| post))
                            (Some (Tm pi (pre |> tms <| post), empty))
  | NoMatchNFB':
      forall p pi pre tms post tup,
        match_pattern' p (Tm pi (pre |> tms <| post)) (Some tup) ->
        match_pattern' (PatNFB p)
                       (Tm pi (pre |> tms <| post)) None
  | MatchLabel':
      forall lbl pi pre tms tms' post,
        match_pattern' (PatLabel lbl)
                       (Tm pi (pre |> tms <| Tm lbl tms' :: post))
                 (Some (Tm pi (pre |> tms & Tm lbl tms' <| post), empty))
  | NoMatchLabel':
      forall lbl lbl' pi pre tms tms' post,
        lbl <> lbl' ->
        match_pattern' (PatLabel lbl)
                       (Tm pi (pre |> tms <| Tm lbl' tms' :: post)) None
  | MatchAny':
      forall pi pre tms post tm,
        match_pattern' (PatAny)
                       (Tm pi (pre |> tms <| tm :: post))
                 (Some (Tm pi (pre |> tms & tm <| post), empty))
  | NoMatchAny':
      forall pi pre tms,
        match_pattern' (PatAny)
                       (Tm pi (pre |> tms <|)) None
  | MatchChoiceL':
    forall p1 p2 pi pre tms post tm M,
      match_pattern' p1 (Tm pi (pre |> tms <| post)) (Some (tm, M)) ->
      match_pattern' (PatChoice p1 p2) (Tm pi (pre |> tms <| post)) (Some (tm, M))
  | MatchChoiceR':
    forall p1 p2 pi pre tms post tm M,
      match_pattern' p1 (Tm pi (pre |> tms <| post)) None ->
      match_pattern' p2 (Tm pi (pre |> tms <| post)) (Some (tm, M)) ->
      match_pattern' (PatChoice p1 p2) (Tm pi (pre |> tms <| post)) (Some (tm, M))
  | NoMatchChoice':
    forall p1 p2 pi pre tms post,
      match_pattern' p1 (Tm pi (pre |> tms <| post)) None ->
      match_pattern' p2 (Tm pi (pre |> tms <| post)) None ->
      match_pattern' (PatChoice p1 p2) (Tm pi (pre |> tms <| post)) None
  | MatchSeq':
    forall p1 p2 pi pre tms post tm1 tm2 M1 M2,
      match_pattern' p1 (Tm pi (pre |> tms <| post)) (Some (tm1, M1)) ->
      match_pattern' p2 tm1 (Some (tm2, M2)) ->
      match_pattern' (PatSeq p1 p2) (Tm pi (pre |> tms <| post)) (Some (tm2, (M1 & M2)))
  | NoMatchSeqL':
    forall p1 p2 pi pre tms post,
      match_pattern' p1 (Tm pi (pre |> tms <| post)) None ->
      match_pattern' (PatSeq p1 p2) (Tm pi (pre |> tms <| post)) None
  | NoMatchSeqR':
    forall p1 p2 pi pre tms post tm1 M1,
      match_pattern' p1 (Tm pi (pre |> tms <| post)) (Some (tm1, M1)) ->
      match_pattern' p2 tm1 None ->
      match_pattern' (PatSeq p1 p2) (Tm pi (pre |> tms <| post)) None
  | MatchChildren':
    forall p1 p2 pi pre tms tms' post lbl tm M1 M2,
      match_pattern' p1
                     (Tm pi (pre |> tms <| Tm lbl tms' :: post))
               (Some (Tm pi (pre |> tms & Tm lbl tms' <| post), M1)) ->
      match_pattern' p2 (Tm lbl (|> <| tms')) (Some (tm, M2)) ->
      match_pattern' (PatChildren p1 p2)
                    (Tm pi (pre |> tms <| Tm lbl tms' :: post))
              (Some (Tm pi (pre |> tms & Tm lbl tms' <| post), M1 & M2))
  | NoMatchChildrenL':
    forall p1 p2 pi pre tms post,
      match_pattern' p1 (Tm pi (pre |> tms <| post)) None ->
      match_pattern' (PatChildren p1 p2) (Tm pi (pre |> tms <| post)) None
  | NoMatchChildrenL2':
    forall p1 p2 pi pre tms tms' post post' M,
      match_pattern' p1 (Tm pi (pre |> tms <| post))
                  (Some (Tm pi (pre |> tms ++ tms' <| post'), M)) ->
      length tms' <> 1 ->
      match_pattern' (PatChildren p1 p2) (Tm pi (pre |> tms <| post)) None
  | NoMatchChildrenR':
    forall p1 p2 pi pre tms tms' post lbl M,
      match_pattern' p1 (Tm pi (pre |> tms <| Tm lbl tms' :: post))
                  (Some (Tm pi (pre |> tms & Tm lbl tms' <| post), M)) ->
      match_pattern' p2 (Tm lbl (|> <| tms')) None ->
      match_pattern' (PatChildren p1 p2)
                     (Tm pi (pre |> tms <| Tm lbl tms' :: post)) None
  | MatchNot':
    forall p pi pre tms post tm,
      match_pattern' p (Tm pi (pre |> tms <| tm :: post)) None ->
      match_pattern' (PatNeg p) (Tm pi (pre |> tms <| tm :: post))
                          (Some (Tm pi (pre |> tms & tm <| post), empty))
  | NoMatchNot':
    forall p pi pre tms post tm tup,
      match_pattern' p (Tm pi (pre |> tms <| tm :: post)) (Some tup) ->
      match_pattern' (PatNeg p) (Tm pi (pre |> tms <| tm :: post)) None
  | MatchOptionYes':
    forall p pi pre tms post tm M,
      match_pattern' p (Tm pi (pre |> tms <| post)) (Some (tm, M)) ->
      match_pattern' (PatOption p) (Tm pi (pre |> tms <| post))
                                   (Some (tm, M))
  | MatchOptionNo':
    forall p pi pre tms post,
      match_pattern' p (Tm pi (pre |> tms <| post)) None ->
      match_pattern' (PatOption p) (Tm pi (pre |> tms <| post))
                             (Some (Tm pi (pre |> tms <| post), empty))
  | MatchManyMore':
    forall p pi pre tms tms' post post' tm M1 M2,
      match_pattern' p (Tm pi (pre |> tms <| post))
                 (Some (Tm pi (pre |> tms ++ tms' <| post'), M1)) ->
      tms' <> nil ->
      match_pattern' (PatMany p) (Tm pi (pre |> tms ++ tms' <| post'))
                                 (Some (tm, M2)) ->
      match_pattern' (PatMany p) (Tm pi (pre |> tms <| post)) (Some (tm, (M1 & M2)))
  | MatchManyDone':
    forall p pi pre tms post,
      match_pattern' p (Tm pi (pre |> tms <| post)) None ->
      match_pattern' (PatMany p) (Tm pi (pre |> tms <| post))
                           (Some (Tm pi (pre |> tms <| post), empty))
  | MatchAction':
    forall p f pi pre tms tms' post post' M,
      match_pattern' p (Tm pi (pre |> tms <| post))
                 (Some (Tm pi (pre |> tms ++ tms' <| post'), M)) ->
      f tms' = true ->
      match_pattern' (PatAction p f)
                     (Tm pi (pre |> tms <| post))
               (Some (Tm pi (pre |> tms ++ tms' <| post'), M))
  | NoMatchAction':
    forall p pi pre tms post f,
      match_pattern' p (Tm pi (pre |> tms <| post)) None ->
      match_pattern' (PatAction p f) (Tm pi (pre |> tms <| post)) None
  | NoMatchActionFun':
    forall p pi pre tms tms' post post' M f,
      match_pattern' p (Tm pi (pre |> tms <| post))
                 (Some (Tm pi (pre |> tms ++ tms' <| post'), M)) ->
      f tms' = false ->
      match_pattern' (PatAction p f) (Tm pi (pre |> tms <| post)) None.

(*
  Inductive match_pattern' : nat -> pattern -> term -> term -> bindings -> Prop :=
  | MatchCtx':
    forall n p pi pre tm1 tm2 post M,
      (* TODO: I would rather not have the Foralls here *)
      Forall is_term pre ->
      Forall is_term post ->
      match_pattern' n p tm1 tm2 M ->
      match_pattern' (S n) p
                     (Tm pi (pre & tm1 ++ post))
                     (Tm pi (pre & tm2 ++ post)) M
  | MatchBind':
    forall n p pi pre tms tms' post post' x M,
      match_pattern' n p (Tm pi (pre |> tms <| post))
                     (Tm pi (pre |> tms ++ tms' <| post')) M ->
      match_pattern' (S n) (PatBind p x)
                     (Tm pi (pre |> tms <| post))
                     (Tm pi (pre |> tms ++ tms' <| post')) (M & x ~ tms')
  | MatchStart':
    forall pi post,
      match_pattern' 0 PatStart
                     (Tm pi (|> <| post))
                     (Tm pi (|> <| post)) empty
  | MatchEnd':
    forall pi pre,
      match_pattern' 0 PatEnd
                     (Tm pi (pre |> <|))
                     (Tm pi (pre |> <|)) empty
  | MatchIn':
      forall pi pre tms post,
        match_pattern' 0 (PatIn pi)
                       (Tm pi (pre |> tms <| post))
                       (Tm pi (pre |> tms <| post)) empty
  | MatchFB':
      forall n p pi pre tms post tm M,
        match_pattern' n p (Tm pi (pre |> tms <| post)) tm M ->
        match_pattern' (S n) (PatFB p)
                       (Tm pi (pre |> tms <| post))
                       (Tm pi (pre |> tms <| post)) empty
  | MatchNFB':
      forall n p pi pre tms post,
        nomatch_pattern' n p (Tm pi (pre |> tms <| post)) ->
        match_pattern' (S n) (PatNFB p)
                       (Tm pi (pre |> tms <| post))
                       (Tm pi (pre |> tms <| post)) empty
  | MatchLabel':
      forall lbl pi pre tms tms' post,
        match_pattern' 0 (PatLabel lbl)
                       (Tm pi (pre |> tms <| Tm lbl tms' :: post))
                       (Tm pi (pre |> tms & Tm lbl tms' <| post)) empty
  | MatchAny':
      forall pi pre tms post tm,
        match_pattern' 0 (PatAny)
                         (Tm pi (pre |> tms <| tm :: post))
                         (Tm pi (pre |> tms & tm <| post)) empty
(*
  | MatchChoiceL:
    forall p1 p2 pi pre tms post tm M,
      match_pattern p1 (Tm pi (pre |> tms <| post)) tm M ->
      match_pattern (PatChoice p1 p2) (Tm pi (pre |> tms <| post)) tm M
  | MatchChoiceR:
    forall p1 p2 pi pre tms post tm M,
      nomatch_pattern p1 (Tm pi (pre |> tms <| post)) ->
      match_pattern p2 (Tm pi (pre |> tms <| post)) tm M ->
      match_pattern (PatChoice p1 p2) (Tm pi (pre |> tms <| post)) tm M
  | MatchSeq:
    forall p1 p2 pi pre tms post tm1 tm2 M1 M2,
      match_pattern p1 (Tm pi (pre |> tms <| post)) tm1 M1 ->
      match_pattern p2 tm1 tm2 M2 ->
      match_pattern (PatSeq p1 p2) (Tm pi (pre |> tms <| post)) tm2 (M1 & M2)
  | MatchChildren:
    forall p1 p2 pi pre tms tms' post lbl tm M1 M2,
      match_pattern p1 (Tm pi (pre |> tms <| Tm lbl tms' :: post))
                       (Tm pi (pre |> tms & Tm lbl tms' <| post)) M1 ->
      match_pattern p2 (Tm lbl (|> <| tms')) tm M2 ->
      match_pattern (PatChildren p1 p2)
                    (Tm pi (pre |> tms <| Tm lbl tms' :: post))
                    (Tm pi (pre |> tms & Tm lbl tms' <| post)) (M1 & M2)
  | MatchNot:
    forall p pi pre tms post tm,
      nomatch_pattern p (Tm pi (pre |> tms <| tm :: post)) ->
      match_pattern (PatNeg p) (Tm pi (pre |> tms <| tm :: post))
                               (Tm pi (pre |> tms & tm <| post)) empty
  | MatchOptionYes:
    forall p pi pre tms post tm M,
      match_pattern p (Tm pi (pre |> tms <| post)) tm M ->
      match_pattern (PatOption p) (Tm pi (pre |> tms <| post))
                                  tm M
  | MatchOptionNo:
    forall p pi pre tms post,
      nomatch_pattern p (Tm pi (pre |> tms <| post)) ->
      match_pattern (PatOption p) (Tm pi (pre |> tms <| post))
                                  (Tm pi (pre |> tms <| post)) empty
  | MatchManyMore:
    forall p pi pre tms tms' post post' tm M1 M2,
      match_pattern p (Tm pi (pre |> tms <| post))
                      (Tm pi (pre |> tms ++ tms' <| post')) M1 ->
      tms' <> nil ->
      match_pattern (PatMany p) (Tm pi (pre |> tms ++ tms' <| post')) tm M2 ->
      match_pattern (PatMany p) (Tm pi (pre |> tms <| post)) tm (M1 & M2)
  | MatchManyDone:
    forall p pi pre tms post,
      nomatch_pattern p (Tm pi (pre |> tms <| post)) ->
      match_pattern (PatMany p) (Tm pi (pre |> tms <| post))
                                (Tm pi (pre |> tms <| post)) empty
  | MatchAction:
    forall p f pi pre tms tms' post post' M,
      match_pattern p (Tm pi (pre |> tms <| post))
                      (Tm pi (pre |> tms ++ tms' <| post')) M ->
      f tms' = true ->
      match_pattern (PatAction p f) (Tm pi (pre |> tms <| post))
                                    (Tm pi (pre |> tms ++ tms' <| post')) M
*)
  with
    nomatch_pattern' : nat -> pattern -> term -> Prop :=
    | NoMatchBind':
      forall n p pi pre tms post x,
        nomatch_pattern' n p (Tm pi (pre |> tms <| post)) ->
        nomatch_pattern' (S n) (PatBind p x) (Tm pi (pre |> tms <| post))
    | NoMatchStart':
      forall pi pre tms post,
        pre ++ tms <> nil ->
        nomatch_pattern' 0 PatStart (Tm pi (pre |> tms <| post))
    | NoMatchEnd':
      forall pi pre tms post,
        tms ++ post <> nil ->
        nomatch_pattern' 0 PatEnd (Tm pi (pre |> tms <| post))
    | NoMatchIn':
      forall lbl pi pre tms post,
        lbl <> pi ->
        nomatch_pattern' 0 (PatIn lbl) (Tm pi (pre |> tms <| post))
    | NoMatchFB':
      forall n p pi pre tms post,
        nomatch_pattern' n p (Tm pi (pre |> tms <| post)) ->
        nomatch_pattern' (S n) (PatFB p) (Tm pi (pre |> tms <| post))
    | NoMatchNFB':
      forall n p pi pre tms post tm M,
        match_pattern' n p (Tm pi (pre |> tms <| post)) tm M ->
        nomatch_pattern' (S n) (PatNFB p) (Tm pi (pre |> tms <| post)).
(*
    | NoMatchLabel:
      forall lbl lbl' pi pre tms tms' post,
        lbl <> lbl' ->
        nomatch_pattern (PatLabel lbl) (Tm pi (pre |> tms <| Tm lbl' tms' :: post))
    | NoMatchAny:
      forall pi pre tms,
        nomatch_pattern (PatAny) (Tm pi (pre |> tms <|))
    | NoMatchChoice:
      forall p1 p2 pi pre tms post,
        nomatch_pattern p1 (Tm pi (pre |> tms <| post)) ->
        nomatch_pattern p2 (Tm pi (pre |> tms <| post)) ->
        nomatch_pattern (PatChoice p1 p2) (Tm pi (pre |> tms <| post))
    | NoMatchSeqL:
      forall p1 p2 pi pre tms post,
        nomatch_pattern p1 (Tm pi (pre |> tms <| post)) ->
        nomatch_pattern (PatSeq p1 p2) (Tm pi (pre |> tms <| post))
    | NoMatchSeqR:
      forall p1 p2 pi pre tms post tm1 M1,
        match_pattern p1 (Tm pi (pre |> tms <| post)) tm1 M1 ->
        nomatch_pattern p2 tm1 ->
        nomatch_pattern (PatSeq p1 p2) (Tm pi (pre |> tms <| post))
    | NoMatchChildrenL:
      forall p1 p2 pi pre tms post,
        nomatch_pattern p1 (Tm pi (pre |> tms <| post)) ->
        nomatch_pattern (PatChildren p1 p2) (Tm pi (pre |> tms <| post))
    | NoMatchChildrenL2:
      forall p1 p2 pi pre tms tms' post post' M,
        match_pattern p1 (Tm pi (pre |> tms <| post))
                         (Tm pi (pre |> tms ++ tms' <| post')) M ->
        length tms' <> 1 ->
        nomatch_pattern (PatChildren p1 p2) (Tm pi (pre |> tms <| post))
    | NoMatchChildrenR:
      forall p1 p2 pi pre tms tms' post lbl M,
        match_pattern p1 (Tm pi (pre |> tms <| Tm lbl tms' :: post))
                         (Tm pi (pre |> tms & Tm lbl tms' <| post)) M ->
        nomatch_pattern p2 (Tm lbl (|> <| tms')) ->
        nomatch_pattern (PatChildren p1 p2) (Tm pi (pre |> tms <| Tm lbl tms' :: post))
    | NoMatchNot:
      forall p pi pre tms post tm M,
        match_pattern p (Tm pi (pre |> tms <| tm :: post))
                        (Tm pi (pre |> tms & tm <| post)) M ->
        nomatch_pattern (PatNeg p) (Tm pi (pre |> tms <| tm :: post))
    | NoMatchAction:
      forall p pi pre tms post f,
        nomatch_pattern p (Tm pi (pre |> tms <| post)) ->
        nomatch_pattern (PatAction p f) (Tm pi (pre |> tms <| post))
    | NoMatchActionFun:
      forall p pi pre tms tms' post post' M f,
        match_pattern p (Tm pi (pre |> tms <| post))
                        (Tm pi (pre |> tms ++ tms' <| post')) M ->
        f tms' = false ->
        nomatch_pattern (PatAction p f) (Tm pi (pre |> tms <| post)).
*)
*)
  Lemma select_is_term_absurd:
    forall pre pre' tms post post' tm,
      Forall is_term pre ->
      Forall is_term post ->
      pre & tm ++ post <> (pre' |> tms <| post').
  Proof using.
    introv Hall1 Hall2.
    rew_list.
    gen tms pre' post'.
    inductions Hall1; introv.
    - destruct pre'; rew_list.
      + intros contra. inverts contra.
        forwards (_ & Hall'): Forall_app_inv Hall2.
        inverts Hall'. inverts H1.
      + intros contra. inverts contra.
        forwards (_ & Hall'): Forall_app_inv Hall2.
        inverts Hall'. inverts H1.
    - destruct pre'; rew_list.
      + intros contra.  inverts contra. inverts H.
      + intros contra. inverts* contra.
  Qed.

  Lemma select_eq_inv:
    forall pre pre' tms tms' post post',
      Forall is_term pre ->
      Forall is_term tms ->
      Forall is_term post ->
      (pre' |> tms' <| post') = (pre |> tms <| post) ->
      pre = pre' /\ tms = tms' /\ post = post'.
  Proof using.
    introv Hall1 Hall2 Hall3 Heq.
    gen pre'. induction pre; intros.
    - destruct pre'.
      + split*. rew_list in Heq. inverts Heq.
        clear Hall1. gen tms'. induction tms; introv Heq.
        * destruct tms'.
          -- rew_list in Heq. inverts* Heq.
          -- rew_list in Heq. inverts Heq.
             forwards* (_ & Hall): Forall_app_inv.
             inverts Hall. inverts H1.
        * destruct tms'; rew_list in Heq.
          -- inverts Heq. inverts Hall2. inverts H1.
          -- inverts Heq. inverts Hall2. forwards*: IHtms.
             splits*. fequals*.
      + rew_list in Heq. inverts Heq.
        gen pre'. induction tms; introv Heq.
        * rew_list in Heq. destruct pre'.
          -- rew_list in Heq. inverts Heq.
          -- rew_list in Heq. inverts Heq.
             forwards* (_ & Hall): Forall_app_inv.
             inverts Hall. inverts H1.
        * rew_list in Heq. destruct pre'.
          -- rew_list in Heq. inverts Heq.
             inverts Hall2. inverts H2.
          -- rew_list in Heq. inverts Heq.
             inverts Hall2.
             forwards* (absurd & _): IHtms. inverts absurd.
    - inverts Hall1. destruct pre'.
      + rew_list in Heq. inverts Heq. inverts H1.
      + rew_list in Heq. inverts Heq.
        forwards*: IHpre. splits*. fequals*.
  Qed.

  Lemma is_matching_term_select_inv:
    forall lbl pre tms post,
      is_matching_term (Tm lbl (pre |> tms <| post)) ->
      Forall is_term pre /\ Forall is_term tms /\ Forall is_term post.
  Proof using.
    introv Hmtm. inverts Hmtm.
    - false* select_is_term_absurd H1.
    - symmetry in H0. forwards* (-> & -> & ->): select_eq_inv H0.
  Qed.

  Lemma is_matching_term_ctx_inv:
    forall lbl pre tm post,
      Forall is_term pre ->
      Forall is_term post ->
      is_matching_term (Tm lbl (pre & tm ++ post)) ->
      is_matching_term tm.
  Proof using.
    introv Hall1 Hall2 Hmtm. inverts Hmtm as Hall1' Hall2' Hmtm Heq.
    - gen pre0. induction pre; destruct pre0; intros; rew_list in *.
      + inverts* Heq.
      + inverts Heq.
        forwards* (Hall1'' & Hall2''): Forall_app_inv.
        inverts Hall2''. false* is_term_not_is_matching.
      + inverts Heq. inverts Hall1. false* is_term_not_is_matching.
      + inverts Heq. inverts Hall1. inverts Hall1'.
        applys* IHpre. rew_list*.
    - gen pre0. induction pre; destruct pre0; intros; rew_list in *.
      + inverts Heq. forwards* (_ & Hall): Forall_app_inv.
        inverts Hall as contra. inverts contra.
      + inverts Heq. forwards* (_ & Hall): Forall_app_inv.
        inverts Hall as contra. inverts contra.
      + inverts Heq. inverts Hall1 as contra. inverts contra.
      + inverts Heq. inverts Hall1. inverts* Hall1'.
  Qed.

  Lemma match_pattern_preserves_term_size:
    forall p tm tm' M,
      match_pattern p tm tm' M ->
      term_size tm = term_size tm'.
  Proof using.
    introv Hmatch.
    induction* Hmatch.
    - repeat rewrites term_size_app. simpls*.
    - repeat rewrites term_size_app. fequal.
      simpls. fequals.
      repeat rewrites terms_size_app. simpls. nat_math.
    - repeat rewrites term_size_app. fequal.
      simpls. fequals.
      repeat rewrites terms_size_app. simpls. nat_math.
    - nat_math.
    - repeat rewrites term_size_app. fequal.
      simpls. fequals.
      repeat rewrites terms_size_app. simpls. nat_math.
    - nat_math.
  Qed.

  (* TODO: Can we show that we always move the maximal number of
  terms? Could this imply determinism? *)
  Lemma match_pattern_moves_terms:
    forall p pi pre tms post tm' M,
      Forall is_term pre ->
      Forall is_term tms ->
      Forall is_term post ->
      match_pattern p (Tm pi (pre |> tms <| post)) tm' M ->
      exists tms' post',
        tm' = Tm pi (pre |> tms ++ tms' <| post') /\ post = tms' ++ post'.
  Proof using.
    introv Hall1 Hall2 Hall3 Hmatch. remember (Tm pi (pre |> tms <| post)) as tm.
    gen pre tms post. induction* Hmatch; intros; inverts Heqtm.
    - false* select_is_term_absurd H3. (* TODO: Should match goal *)
    - forwards* (-> & -> & ->): select_eq_inv H1.
      eexists nil. exists post. rew_list*.
    - forwards* (-> & -> & ->): select_eq_inv H1.
      eexists nil. eexists nil. rew_list*.
    - forwards* (-> & -> & ->): select_eq_inv H1.
      eexists nil. exists post. rew_list*.
    - forwards* (-> & -> & ->): select_eq_inv H1.
      eexists nil. exists post. rew_list*.
    - forwards* (-> & -> & ->): select_eq_inv H2.
      eexists nil. exists post. rew_list*.
    - forwards* (-> & -> & Heq): select_eq_inv H1.
    - forwards* (-> & -> & Heq): select_eq_inv H1.
    - forwards* (-> & -> & ->): select_eq_inv H1.
      forwards* (tms' & post' & -> & ->): IHHmatch1 pre tms post.
      forwards~ (Hall31 & Hall32): Forall_app_inv Hall3.
      forwards* (tms'' & post'' & -> & ->): IHHmatch2 pre (tms ++ tms') post'.
      { applys* Forall_app. }
      exists (tms' ++ tms'') post''. rew_list*.
    - forwards* (-> & -> & ->): select_eq_inv H2.
    - forwards* (-> & -> & ->): select_eq_inv H2.
      eexists nil. exists post. rew_list*.
    - forwards* (-> & -> & ->): select_eq_inv H2.
      forwards* (tms'' & post'' & Heq & ->): IHHmatch1 pre tms post.
      inverts Heq.
      forwards~ (Hall31 & Hall32): Forall_app_inv Hall3.
      forwards* (_ & Heq' & ->): select_eq_inv H1.
      { applys* Forall_app. }
      forwards~ ->: app_cancel_l Heq'.
      forwards* (tms'' & post'' & -> & ->): IHHmatch2 pre (tms ++ tms') post'.
      { applys* Forall_app. }
      exists (tms' ++ tms'') post''. rew_list*.
    - forwards* (-> & -> & ->): select_eq_inv H2.
      eexists nil. exists post. rew_list*.
  Qed.

  Lemma match_pattern_preserves_matching_term:
    forall tm tm' p M,
      is_matching_term tm ->
      match_pattern p tm tm' M ->
      is_matching_term tm'.
  Proof using.
    intros tm. induction_wf IH: term_size tm. unfolds measure.
    introv Hmtm Hmatch. gen tm tm'. inductions p; intros.
    - inverts~ Hmatch. forwards~ Hmtm': is_matching_term_ctx_inv Hmtm.
      forwards*: IH Hmtm'.
    - inverts~ Hmatch. forwards~ Hmtm': is_matching_term_ctx_inv Hmtm.
      forwards*: IH Hmtm'.
    - inverts~ Hmatch. forwards~ Hmtm': is_matching_term_ctx_inv Hmtm.
      forwards*: IH Hmtm'.
    - inverts~ Hmatch. forwards~ Hmtm': is_matching_term_ctx_inv Hmtm.
      forwards*: IH Hmtm'.
    - inverts~ Hmatch. forwards~ Hmtm': is_matching_term_ctx_inv Hmtm.
      forwards*: IH Hmtm'.
    - inverts~ Hmatch.
      + forwards~ Hmtm': is_matching_term_ctx_inv Hmtm.
        forwards*: IH Hmtm'.
      + forwards~ (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        inverts Hall3 as Htm Hall3.
        constructors*.
    - inverts~ Hmatch.
      + forwards~ Hmtm': is_matching_term_ctx_inv Hmtm.
        forwards*: IH Hmtm'.
      + forwards~ (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        inverts Hall3 as Htm Hall3.
        constructors*.
    - inverts~ Hmatch.
      + forwards~ Hmtm': is_matching_term_ctx_inv Hmtm.
        forwards*: IH Hmtm'.
      + forwards* (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
      + forwards~ (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        applys* IHp2.
    - inverts~ Hmatch.
      + forwards~ Hmtm': is_matching_term_ctx_inv Hmtm.
        forwards*: IH Hmtm'.
      + forwards~ Hmtm1: IHp1 H1. forwards~: IHp2 H5.
        introv Hlt Hmtm' Hmatch. applys* IH.
        asserts Heq: (term_size (Tm pi (pre |> tms <| post)) = term_size tm1).
        { apply* match_pattern_preserves_term_size. }
        nat_math.
    - inverts~ Hmatch.
      + forwards~ Hmtm': is_matching_term_ctx_inv Hmtm.
        forwards*: IH Hmtm'.
      + forwards~ Hmtm1: IHp1 H1.
    - inverts~ Hmatch.
      + forwards~ Hmtm': is_matching_term_ctx_inv Hmtm.
        forwards*: IH Hmtm'.
      + forwards~ (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        inverts Hall3.
        constructors*.
    - inverts~ Hmatch.
      + forwards~ Hmtm': is_matching_term_ctx_inv Hmtm.
        forwards*: IH Hmtm'.
      + forwards* (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
    - inverts~ Hmatch.
      + forwards~ Hmtm': is_matching_term_ctx_inv Hmtm.
        forwards*: IH Hmtm'.
      + forwards~ Hmtm': IHp H0.
        forwards~ (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm'.
        forwards~ (Hall21 & Hall22): Forall_app_inv Hall2.
        forwards~ (tms'' & post'' & -> & ->): match_pattern_moves_terms H2.
        forwards~ (Hall31 & Hall32): Forall_app_inv Hall3.
        constructors*.
        applys* Forall_app.
    - inverts~ Hmatch.
      + forwards~ Hmtm': is_matching_term_ctx_inv Hmtm.
        forwards*: IH Hmtm'.
      + forwards* (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
    - inverts~ Hmatch.
      + forwards~ Hmtm': is_matching_term_ctx_inv Hmtm.
        forwards*: IH Hmtm'.
      + forwards* (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
  Qed.

  (* TODO: Create a version of match_pattern with an explicit
  height n of derivation and do induction over n1 + n2? *)
(*
  Lemma match_pattern_deterministic':
    forall n m p tm tm1 tm2 M1 M2,
      is_matching_term tm ->
      match_pattern' n p tm tm1 M1 ->
      match_pattern' m p tm tm2 M2 ->
      tm1 = tm2 /\ M1 = M2.
  Proof using.
    intros n m.
    remember (n + m)%nat as sum.
    gen n m. induction_wf IH: ????? sum. unfolds measure.
    (* TODO: Still only know how to do one at a time... *)
    introv Hmtm Hmatch1 Hmatch2.
*)
  Lemma match_pattern_deterministic:
    forall p tm tm1 tm2 M1 M2,
      is_matching_term tm ->
      match_pattern p tm tm1 M1 ->
      match_pattern p tm tm2 M2 ->
      tm1 = tm2 /\ M1 = M2.
  Proof using.
    introv Hmtm Hmatch1 Hmatch2.
    gen tm2 M2.
    induction Hmatch1; intros; inverts Hmatch2;
      try match goal with
      | H : (_ |> _ <| _) = _ & _ ++ _ |- _ =>
          symmetry in H; false* select_is_term_absurd H
      | H : _ & _ ++ _ = (_ |> _ <| _) |- _ =>
          false* select_is_term_absurd H
      end.
(*
    - forwards~ Hmtm': is_matching_term_ctx_inv Hmtm.
      (* ctx_inv lemma *) admit.
    - forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
      forwards* (-> & -> & ->): select_eq_inv H3.
      forwards* (Heq & -> & Hnmatch): IHHmatch1.
      inverts Heq.
      forwards* Hmtm': match_pattern_preserves_matching_term.
      forwards (Hall1' & Hall2' & Hall3'): is_matching_term_select_inv Hmtm'.
      forwards* (_ & Heq' & ->): select_eq_inv H0.
      forwards~ ->: app_cancel_l Heq'.
      splits*. intros contra. inverts contra.
      forwards* (-> & -> & ->): select_eq_inv H6.
    - rew_list in *. subst*. admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
      forwards* (-> & -> & ->): select_eq_inv H2.
      forwards* (-> & -> & Hnmatch): IHHmatch1.
      splits*. intros contra. inverts contra.
    - forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
      forwards* (-> & -> & ->): select_eq_inv H2.
      forwards* (Heq & -> & Hnmatch): IHHmatch1.
    - forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
      forwards* (-> & -> & ->): select_eq_inv H3.
      admit. (* TODO: No induction hypothesis talking about second match :( *)
    - splits*. intros contra. inverts contra.
    - forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
      forwards* (-> & -> & ->): select_eq_inv H2.
      admit.
    - admit.
    - admit.
    - admit.
    -
*)
  Admitted.

  Lemma nomatch_is_negation:
    forall p tm tm' M,
      is_matching_term tm ->
      nomatch_pattern p tm ->
      ~match_pattern p tm tm' M.
  Proof using.
    introv Hmtm Hnmatch contra. inductions p.
    - inverts Hnmatch. inverts contra.
      + false* select_is_term_absurd H1.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards* (-> & -> & ->): select_eq_inv H3.
    - inverts Hnmatch. inverts contra.
      + false* select_is_term_absurd H1.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards* (-> & -> & ->): select_eq_inv H3.
    - inverts Hnmatch. inverts contra.
      + false* select_is_term_absurd H1.
      + forwards* (-> & -> & ->): select_eq_inv H3.
    - inverts Hnmatch. inverts contra.
      + false* select_is_term_absurd H1.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards* (-> & -> & ->): select_eq_inv H2.
    - inverts Hnmatch. inverts contra.
      + false* select_is_term_absurd H1.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards* (-> & -> & ->): select_eq_inv H2.
    - inverts Hnmatch. inverts contra.
      + false* select_is_term_absurd H1.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards* (-> & -> & Heq): select_eq_inv H3.
        inverts* Heq.
    - inverts Hnmatch. inverts contra.
      + false* select_is_term_absurd H0.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards* (-> & -> & Heq): select_eq_inv H1.
        inverts Heq.
    - inverts Hnmatch. inverts contra.
      + false* select_is_term_absurd H0.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards* (-> & -> & ->): select_eq_inv H5.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards* (-> & -> & ->): select_eq_inv H5.
    - inverts Hnmatch.
      + inverts contra.
        * false* select_is_term_absurd H1.
        * forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
          forwards* (-> & -> & ->): select_eq_inv H4.
      + inverts contra.
        * false* select_is_term_absurd H0.
        * forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
          forwards~ (-> & -> & ->): select_eq_inv H5.
          forwards (-> & Heq): match_pattern_deterministic H1 H7; eauto.
          forwards*: IHp2 H3.
          applys* match_pattern_preserves_matching_term.
    - inverts Hnmatch.
      + inverts contra.
        * false* select_is_term_absurd H1.
        * forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
          forwards* (-> & -> & ->): select_eq_inv H4.
      + inverts contra.
        * false* select_is_term_absurd H0.
        * forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
          forwards~ (-> & -> & ->): select_eq_inv H5.
          forwards (Heq & ->): match_pattern_deterministic H1 H7; eauto.
          inverts Heq. inverts Hall3.
          forwards~ (_ & Heq & _): select_eq_inv H0. applys~ Forall_last.
          apply app_cancel_l in Heq. subst*.
      + inverts contra.
        * false* select_is_term_absurd H0.
        * forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
          forwards~ (-> & -> & Heq): select_eq_inv H5.
          inverts Heq. applys IHp2 H3 H8.
          inverts Hmtm.
          -- false* select_is_term_absurd H0.
          -- forwards* (-> & -> & Heq): select_eq_inv H0.
             subst. inverts H6. inverts H10. constructors*.
    - inverts Hnmatch. inverts contra.
      + false* select_is_term_absurd H1.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards~ (-> & -> & Heq): select_eq_inv H3.
        inverts *Heq.
    - inverts Hnmatch.
    - inverts Hnmatch.
    - inverts Hnmatch. inverts contra.
      + false* select_is_term_absurd H0.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards* (-> & -> & ->): select_eq_inv H4.
    - inverts Hnmatch.
      + inverts contra.
        * false* select_is_term_absurd H1.
        * forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
          forwards* (-> & -> & ->): select_eq_inv H4.
      + inverts contra.
        * false* select_is_term_absurd H0.
        * forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
          forwards~ (-> & -> & ->): select_eq_inv H5.
          forwards (Heq & ->): match_pattern_deterministic H1 H7; eauto.
          inverts Heq.
          forwards~ Hmtm': match_pattern_preserves_matching_term H1.
          forwards (Hall1' & Hall2' & Hall3'): is_matching_term_select_inv Hmtm'.
          forwards~ (Hall21 & Hall22): Forall_app_inv Hall2'.
          forwards~ Hmtm'': match_pattern_preserves_matching_term H7.
          forwards (Hall1'' & Hall2'' & Hall3''): is_matching_term_select_inv Hmtm''.
          forwards~ (Hall21' & Hall22'): Forall_app_inv Hall2''.
          forwards~ (_ & Heq' & ->): select_eq_inv H0.
          apply app_cancel_l in Heq'. subst. rewrite H3 in H8. inverts H8.
  Qed.
End Trieste.