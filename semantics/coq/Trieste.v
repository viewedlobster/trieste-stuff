From TLC Require Import LibCore LibTactics LibWf LibList LibNat LibEnv.

Import LibListNotation.

Ltac auto_star ::= try solve [eauto with trieste | intuition eauto].

Local Hint Resolve Forall_last : trieste.
Local Hint Resolve Forall_nil : trieste.
Local Hint Constructors Forall : trieste.
Local Hint Resolve Forall_last_inv : trieste.

Section MiniTrieste.
  Inductive mini_pattern :=
  | MiniPatNat: nat -> mini_pattern
  | MiniPatNot: mini_pattern -> mini_pattern
  | MiniPatChoice: mini_pattern -> mini_pattern -> mini_pattern.

  Inductive match_mini_pattern: mini_pattern -> nat -> option nat -> Prop :=
  | MiniMatchNat:
    forall n,
      match_mini_pattern (MiniPatNat n) n (Some n)
  | MiniNoMatchNat:
    forall n m,
      n <> m ->
      match_mini_pattern (MiniPatNat n) m None
  | MiniMatchNot:
    forall p n,
      match_mini_pattern p n None ->
      match_mini_pattern (MiniPatNot p) n (Some n)
  | MiniNoMatchNot:
    forall p n,
      match_mini_pattern p n (Some n) ->
      match_mini_pattern (MiniPatNot p) n None
  | MiniMatchChoiceL:
    forall p1 p2 n,
      match_mini_pattern p1 n (Some n) ->
      match_mini_pattern (MiniPatChoice p1 p2) n (Some n)
  | MiniMatchChoiceR:
    forall p1 p2 n m,
      match_mini_pattern p1 n None ->
      match_mini_pattern p2 n (Some m) ->
      match_mini_pattern (MiniPatChoice p1 p2) n (Some m)
  | MiniNoMatchChoice:
    forall p1 p2 n,
      match_mini_pattern p1 n None ->
      match_mini_pattern p2 n None ->
      match_mini_pattern (MiniPatChoice p1 p2) n None.
End MiniTrieste.

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

  Hint Extern 2 =>
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

  Inductive match_pattern : pattern -> term -> option (term * bindings) -> Prop :=
  | MatchCtx':
    forall p pi pre tm1 tm2 post M,
      (* TODO: I would rather not have the Foralls here *)
      Forall is_term pre ->
      Forall is_term post ->
      match_pattern p tm1 (Some (tm2, M)) ->
      match_pattern p (Tm pi (pre & tm1 ++ post))
                 (Some (Tm pi (pre & tm2 ++ post), M))
  | NoMatchCtx':
    forall p pi pre tm post,
      (* TODO: I would rather not have the Foralls here *)
      Forall is_term pre ->
      Forall is_term post ->
      match_pattern p tm None ->
      match_pattern p (Tm pi (pre & tm ++ post))
                       None
  | MatchBind':
    forall p pi pre tms tms' post post' x M,
      match_pattern p (Tm pi (pre |> tms <| post))
                 (Some (Tm pi (pre |> tms ++ tms' <| post'), M)) ->
      match_pattern (PatBind p x)
                     (Tm pi (pre |> tms <| post))
               (Some (Tm pi (pre |> tms ++ tms' <| post'), M & x ~ tms'))
  | NoMatchBind':
    forall p pi pre tms post x,
      match_pattern p (Tm pi (pre |> tms <| post)) None ->
      match_pattern (PatBind p x)
                     (Tm pi (pre |> tms <| post)) None
  | MatchStart':
    forall pi post,
      match_pattern PatStart
                     (Tm pi (|> <| post))
               (Some (Tm pi (|> <| post), empty))
  | NoMatchStart':
    forall pi pre tms post,
      pre ++ tms <> nil ->
      match_pattern PatStart
                     (Tm pi (pre |> tms <| post)) None
  | MatchEnd':
    forall pi pre,
      match_pattern PatEnd
                     (Tm pi (pre |> <|))
               (Some (Tm pi (pre |> <|), empty))
  | NoMatchEnd':
    forall pi pre tms post,
      tms ++ post <> nil ->
      match_pattern PatEnd
                     (Tm pi (pre |> tms <| post)) None
  | MatchIn':
      forall pi pre tms post,
        match_pattern (PatIn pi)
                       (Tm pi (pre |> tms <| post))
                 (Some (Tm pi (pre |> tms <| post), empty))
  | NoMatchIn':
      forall pi lbl pre tms post,
        lbl <> pi ->
        match_pattern (PatIn lbl) (Tm pi (pre |> tms <| post)) None
  | MatchFB':
      forall p pi pre tms post tm M,
        match_pattern p (Tm pi (pre |> tms <| post)) (Some (tm, M)) ->
        match_pattern (PatFB p)
                       (Tm pi (pre |> tms <| post))
                 (Some (Tm pi (pre |> tms <| post), empty))
  | NoMatchFB':
      forall p pi pre tms post,
        match_pattern p (Tm pi (pre |> tms <| post)) None ->
        match_pattern (PatFB p)
                       (Tm pi (pre |> tms <| post)) None
  | MatchNFB':
      forall p pi pre tms post,
        match_pattern p (Tm pi (pre |> tms <| post)) None ->
        match_pattern (PatNFB p) (Tm pi (pre |> tms <| post))
                            (Some (Tm pi (pre |> tms <| post), empty))
  | NoMatchNFB':
      forall p pi pre tms post tup,
        match_pattern p (Tm pi (pre |> tms <| post)) (Some tup) ->
        match_pattern (PatNFB p)
                       (Tm pi (pre |> tms <| post)) None
  | MatchLabel':
      forall lbl pi pre tms tms' post,
        match_pattern (PatLabel lbl)
                       (Tm pi (pre |> tms <| Tm lbl tms' :: post))
                 (Some (Tm pi (pre |> tms & Tm lbl tms' <| post), empty))
  | NoMatchLabel':
      forall lbl lbl' pi pre tms tms' post,
        lbl <> lbl' ->
        match_pattern (PatLabel lbl)
                       (Tm pi (pre |> tms <| Tm lbl' tms' :: post)) None
  | MatchAny':
      forall pi pre tms post tm,
        match_pattern (PatAny)
                       (Tm pi (pre |> tms <| tm :: post))
                 (Some (Tm pi (pre |> tms & tm <| post), empty))
  | NoMatchAny':
      forall pi pre tms,
        match_pattern (PatAny)
                       (Tm pi (pre |> tms <|)) None
  | MatchChoiceL':
    forall p1 p2 pi pre tms post tm M,
      match_pattern p1 (Tm pi (pre |> tms <| post)) (Some (tm, M)) ->
      match_pattern (PatChoice p1 p2) (Tm pi (pre |> tms <| post)) (Some (tm, M))
  | MatchChoiceR':
    forall p1 p2 pi pre tms post tm M,
      match_pattern p1 (Tm pi (pre |> tms <| post)) None ->
      match_pattern p2 (Tm pi (pre |> tms <| post)) (Some (tm, M)) ->
      match_pattern (PatChoice p1 p2) (Tm pi (pre |> tms <| post)) (Some (tm, M))
  | NoMatchChoice':
    forall p1 p2 pi pre tms post,
      match_pattern p1 (Tm pi (pre |> tms <| post)) None ->
      match_pattern p2 (Tm pi (pre |> tms <| post)) None ->
      match_pattern (PatChoice p1 p2) (Tm pi (pre |> tms <| post)) None
  | MatchSeq':
    forall p1 p2 pi pre tms post tm1 tm2 M1 M2,
      match_pattern p1 (Tm pi (pre |> tms <| post)) (Some (tm1, M1)) ->
      match_pattern p2 tm1 (Some (tm2, M2)) ->
      match_pattern (PatSeq p1 p2) (Tm pi (pre |> tms <| post)) (Some (tm2, (M1 & M2)))
  | NoMatchSeqL':
    forall p1 p2 pi pre tms post,
      match_pattern p1 (Tm pi (pre |> tms <| post)) None ->
      match_pattern (PatSeq p1 p2) (Tm pi (pre |> tms <| post)) None
  | NoMatchSeqR':
    forall p1 p2 pi pre tms post tm1 M1,
      match_pattern p1 (Tm pi (pre |> tms <| post)) (Some (tm1, M1)) ->
      match_pattern p2 tm1 None ->
      match_pattern (PatSeq p1 p2) (Tm pi (pre |> tms <| post)) None
  | MatchChildren':
    forall p1 p2 pi pre tms tms' post lbl tm M1 M2,
      match_pattern p1
                     (Tm pi (pre |> tms <| Tm lbl tms' :: post))
               (Some (Tm pi (pre |> tms & Tm lbl tms' <| post), M1)) ->
      match_pattern p2 (Tm lbl (|> <| tms')) (Some (tm, M2)) ->
      match_pattern (PatChildren p1 p2)
                    (Tm pi (pre |> tms <| Tm lbl tms' :: post))
              (Some (Tm pi (pre |> tms & Tm lbl tms' <| post), M1 & M2))
  | NoMatchChildrenL':
    forall p1 p2 pi pre tms post,
      match_pattern p1 (Tm pi (pre |> tms <| post)) None ->
      match_pattern (PatChildren p1 p2) (Tm pi (pre |> tms <| post)) None
  | NoMatchChildrenL2':
    forall p1 p2 pi pre tms tms' post post' M,
      match_pattern p1 (Tm pi (pre |> tms <| post))
                  (Some (Tm pi (pre |> tms ++ tms' <| post'), M)) ->
      length tms' <> 1 ->
      match_pattern (PatChildren p1 p2) (Tm pi (pre |> tms <| post)) None
  | NoMatchChildrenR':
    forall p1 p2 pi pre tms tms' post lbl M,
      match_pattern p1 (Tm pi (pre |> tms <| Tm lbl tms' :: post))
                  (Some (Tm pi (pre |> tms & Tm lbl tms' <| post), M)) ->
      match_pattern p2 (Tm lbl (|> <| tms')) None ->
      match_pattern (PatChildren p1 p2)
                     (Tm pi (pre |> tms <| Tm lbl tms' :: post)) None
  | MatchNot':
    forall p pi pre tms post tm,
      match_pattern p (Tm pi (pre |> tms <| tm :: post)) None ->
      match_pattern (PatNeg p) (Tm pi (pre |> tms <| tm :: post))
                          (Some (Tm pi (pre |> tms & tm <| post), empty))
  | NoMatchNot':
    forall p pi pre tms post tm tup,
      match_pattern p (Tm pi (pre |> tms <| tm :: post)) (Some tup) ->
      match_pattern (PatNeg p) (Tm pi (pre |> tms <| tm :: post)) None
  | MatchOptionYes':
    forall p pi pre tms post tm M,
      match_pattern p (Tm pi (pre |> tms <| post)) (Some (tm, M)) ->
      match_pattern (PatOption p) (Tm pi (pre |> tms <| post))
                                   (Some (tm, M))
  | MatchOptionNo':
    forall p pi pre tms post,
      match_pattern p (Tm pi (pre |> tms <| post)) None ->
      match_pattern (PatOption p) (Tm pi (pre |> tms <| post))
                             (Some (Tm pi (pre |> tms <| post), empty))
  | MatchManyMore':
    forall p pi pre tms tms' post post' tm M1 M2,
      match_pattern p (Tm pi (pre |> tms <| post))
                 (Some (Tm pi (pre |> tms ++ tms' <| post'), M1)) ->
      tms' <> nil ->
      match_pattern (PatMany p) (Tm pi (pre |> tms ++ tms' <| post'))
                                 (Some (tm, M2)) ->
      match_pattern (PatMany p) (Tm pi (pre |> tms <| post)) (Some (tm, (M1 & M2)))
  | MatchManyDone':
    forall p pi pre tms post,
      match_pattern p (Tm pi (pre |> tms <| post)) None ->
      match_pattern (PatMany p) (Tm pi (pre |> tms <| post))
                           (Some (Tm pi (pre |> tms <| post), empty))
  | MatchAction':
    forall p f pi pre tms tms' post post' M,
      match_pattern p (Tm pi (pre |> tms <| post))
                 (Some (Tm pi (pre |> tms ++ tms' <| post'), M)) ->
      f tms' = true ->
      match_pattern (PatAction p f)
                     (Tm pi (pre |> tms <| post))
               (Some (Tm pi (pre |> tms ++ tms' <| post'), M))
  | NoMatchAction':
    forall p pi pre tms post f,
      match_pattern p (Tm pi (pre |> tms <| post)) None ->
      match_pattern (PatAction p f) (Tm pi (pre |> tms <| post)) None
  | NoMatchActionFun':
    forall p pi pre tms tms' post post' M f,
      match_pattern p (Tm pi (pre |> tms <| post))
                 (Some (Tm pi (pre |> tms ++ tms' <| post'), M)) ->
      f tms' = false ->
      match_pattern (PatAction p f) (Tm pi (pre |> tms <| post)) None.

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
      match_pattern p tm (Some (tm', M)) ->
      term_size tm = term_size tm'.
  Proof using.
    introv Hmatch.
    remember (Some (tm', M)) as res.
    gen tm' M. induction Hmatch; intros; inverts* Heqres.
    - forwards* IH: IHHmatch. repeat rewrites term_size_app. simpls*.
    - repeat rewrites term_size_app. fequal.
      simpls. fequals.
      repeat rewrites terms_size_app. simpls. nat_math.
    - repeat rewrites term_size_app. fequal.
      simpls. fequals.
      repeat rewrites terms_size_app. simpls. nat_math.
    - forwards* IH1: IHHmatch1. forwards* IH2: IHHmatch2. nat_math.
    - repeat rewrites term_size_app. fequal.
      simpls. fequals.
      repeat rewrites terms_size_app. simpls. nat_math.
    - forwards* IH1: IHHmatch1. forwards* IH2: IHHmatch2. nat_math.
  Qed.

  Lemma match_pattern_moves_terms:
    forall p pi pre tms post tm' M,
      Forall is_term pre ->
      Forall is_term tms ->
      Forall is_term post ->
      match_pattern p (Tm pi (pre |> tms <| post)) (Some (tm', M)) ->
      exists tms' post',
        tm' = Tm pi (pre |> tms ++ tms' <| post') /\ post = tms' ++ post'.
  Proof using.
    introv Hall1 Hall2 Hall3 Hmatch.
    remember (Tm pi (pre |> tms <| post)) as tm.
    remember (Some (tm', M)) as res.
    gen pre tms post tm' M. induction* Hmatch; intros; inverts Heqtm; inverts* Heqres.
    - false* select_is_term_absurd H3. (* TODO: Should match goal *)
    - forwards* (-> & -> & ->): select_eq_inv H1.
    - forwards* (-> & -> & ->): select_eq_inv H1.
      eexists nil. exists post. rew_list*.
    - forwards* (-> & -> & ->): select_eq_inv H1.
      eexists nil. eexists nil. rew_list*.
    - forwards* (-> & -> & ->): select_eq_inv H1.
      eexists nil. exists post. rew_list*.
    - forwards* (-> & -> & ->): select_eq_inv H1.
      eexists nil. exists post. rew_list*.
    - forwards* (-> & -> & Heq): select_eq_inv H1.
      eexists nil. exists post. rew_list*.
    - forwards* (-> & -> & Heq): select_eq_inv H1.
    - forwards* (-> & -> & ->): select_eq_inv H1.
    - forwards* (-> & -> & ->): select_eq_inv H1.
      forwards* (tms' & post' & -> & ->): IHHmatch1 pre tms post tm1 M1.
      forwards~ (Hall31 & Hall32): Forall_app_inv Hall3.
      forwards* (tms'' & post'' & -> & ->): IHHmatch2 pre (tms ++ tms') post'.
      { applys* Forall_app. }
      exists (tms' ++ tms'') post''. rew_list*.
    - forwards* (-> & -> & ->): select_eq_inv H1.
    - forwards* (-> & -> & ->): select_eq_inv H1.
    - forwards* (-> & -> & ->): select_eq_inv H1.
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
    - forwards* (-> & -> & ->): select_eq_inv H1.
      eexists nil. exists post. rew_list*.
  Qed.

  Lemma match_pattern_preserves_matching_term:
    forall tm p tm' M,
      is_matching_term tm ->
      match_pattern p tm (Some (tm', M)) ->
      is_matching_term tm'.
  Proof using.
    intros tm. induction_wf IH: term_size tm. unfolds measure.
    introv Hmtm Hmatch. remember (Some (tm', M)) as res.
    gen tm res tm' M. inductions p; intros; subst; simpls.
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
      + forwards~ Hmtm1: IHp1 H3. forwards~: IHp2 H5.
        introv Hlt Hmtm' Hmatch. applys* IH.
        asserts Heq: (term_size (Tm pi (pre |> tms <| post)) = term_size tm1).
        { apply* match_pattern_preserves_term_size. }
        nat_math.
    - inverts~ Hmatch.
      + forwards~ Hmtm': is_matching_term_ctx_inv Hmtm.
        forwards*: IH Hmtm'.
      + forwards~ Hmtm1: IHp1 H3.
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
      + forwards~ Hmtm': IHp H2.
        forwards~ (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm'.
        forwards~ (Hall21 & Hall22): Forall_app_inv Hall2.
        forwards~ (tms'' & post'' & -> & ->): match_pattern_moves_terms H5.
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

  Lemma ctx_eq_inv:
    forall pre pre' tm tm' post post',
      Forall is_term pre ->
      Forall is_term pre' ->
      Forall is_term post ->
      Forall is_term post' ->
      is_matching_term tm ->
      pre & tm ++ post = pre' & tm' ++ post' ->
      pre = pre' /\ tm = tm' /\ post = post'.
  Proof using.
    introv Hall1 Hall1' Hall2 Hall2' Hmtm Heq.
    inductions pre; intros; destruct pre'; rew_list in *.
    - inverts* Heq.
    - inverts* Heq.
      inverts Hall1' as contra Hall1'.
      false* is_term_not_is_matching.
    - inverts* Heq.
      forwards* (Hall2'1 & Hall2'2): Forall_app_inv.
      inverts Hall2'2 as contra Hall2'2.
      false* is_term_not_is_matching.
    - inverts Heq.
      inverts Hall1 as Htm Hall1.
      inverts Hall1' as Htm' Hall1'.
      forwards* (-> & -> & ->): IHpre pre' tm tm' post post'; rew_list*.
  Qed.

  Lemma match_pattern_deterministic:
    forall tm p res1 res2,
      is_matching_term tm ->
      match_pattern p tm res1 ->
      match_pattern p tm res2 ->
      res1 = res2.
  Proof using.
    intros tm. induction_wf IH: term_size tm. unfolds measure.
    introv Hmtm Hmatch1 Hmatch2.
    gen res2. inductions Hmatch1; intros.
    - forwards~ Hmtm': is_matching_term_ctx_inv Hmtm.
      inverts Hmatch2;
        try match goal with
          | H : (_ |> _ <| _) = _ & _ ++ _ |- _ =>
              symmetry in H; false* select_is_term_absurd H
          | H : _ & _ ++ _ = (_ |> _ <| _) |- _ =>
              false* select_is_term_absurd H
          end.
      + symmetry in H2. forwards* (-> & -> & ->): ctx_eq_inv H2.
        forwards* Heq: IH Hmatch1. inverts* Heq.
      + symmetry in H2. forwards* (-> & -> & ->): ctx_eq_inv H2.
        forwards* Heq: IH Hmatch1. inverts* Heq.
    - forwards~ Hmtm': is_matching_term_ctx_inv Hmtm.
      inverts Hmatch2;
        try match goal with
          | H : (_ |> _ <| _) = _ & _ ++ _ |- _ =>
              symmetry in H; false* select_is_term_absurd H
          | H : _ & _ ++ _ = (_ |> _ <| _) |- _ =>
              false* select_is_term_absurd H
          end.
      + symmetry in H2. forwards* (-> & -> & ->): ctx_eq_inv H2.
        forwards* Heq: IH Hmatch1. inverts* Heq.
      + symmetry in H2. forwards* (-> & -> & ->): ctx_eq_inv H2.
    - inverts Hmatch2.
      + false* select_is_term_absurd H0.
      + false* select_is_term_absurd H0.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards* (-> & -> & ->): select_eq_inv H3.
        forwards* Heq: IHHmatch1. inverts Heq.
        forwards* Hmtm': match_pattern_preserves_matching_term H4.
        forwards (Hall1' & Hall2' & Hall3'): is_matching_term_select_inv Hmtm'.
        forwards* (_ & Heq & _): select_eq_inv H0.
        apply app_cancel_l in Heq. subst*.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards* (-> & -> & ->): select_eq_inv H3.
        forwards* Heq: IHHmatch1. inverts Heq.
    - inverts~ Hmatch2.
      + false* select_is_term_absurd H0.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards* (-> & -> & ->): select_eq_inv H3.
        forwards* Heq: IHHmatch1. inverts Heq.
    - inverts Hmatch2.
      + false* select_is_term_absurd H0.
      + false* select_is_term_absurd H0.
      + vm_compute in H1. subst*.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards* (-> & -> & ->): select_eq_inv H0.
        destruct* tms.
        forwards* (Heq & Heq' & _): select_eq_inv H0. inverts Heq.
    - inverts~ Hmatch2.
      + false* select_is_term_absurd H1.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards* (-> & -> & ->): select_eq_inv H2.
    - inverts Hmatch2.
      + false* select_is_term_absurd H0.
      + false* select_is_term_absurd H0.
      + vm_compute in H1. subst*.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards* (-> & -> & ->): select_eq_inv H0.
        destruct* post.
        forwards* (_ & Heq & Heq'): select_eq_inv H0. inverts Heq.
    - inverts~ Hmatch2.
      + false* select_is_term_absurd H1.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards* (-> & -> & ->): select_eq_inv H2.
    - inverts~ Hmatch2.
      + false* select_is_term_absurd H1.
      + false* select_is_term_absurd H1.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards* (-> & -> & ->): select_eq_inv H2.
    - inverts~ Hmatch2.
      + false* select_is_term_absurd H1.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards* (-> & -> & ->): select_eq_inv H3.
    - inverts~ Hmatch2.
      + false* select_is_term_absurd H1.
      + false* select_is_term_absurd H1.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards* (-> & -> & ->): select_eq_inv H2.
        forwards* Heq: IHHmatch1. inverts Heq.
    - inverts~ Hmatch2.
      + false* select_is_term_absurd H1.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards* (-> & -> & ->): select_eq_inv H2.
        forwards* Heq: IHHmatch1. inverts Heq.
    - inverts~ Hmatch2.
      + false* select_is_term_absurd H1.
      + false* select_is_term_absurd H1.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards* (-> & -> & ->): select_eq_inv H2.
        forwards* Heq: IHHmatch1. inverts Heq.
    - inverts~ Hmatch2.
      + false* select_is_term_absurd H1.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards* (-> & -> & ->): select_eq_inv H2.
        forwards* Heq: IHHmatch1. inverts Heq.
    - inverts~ Hmatch2.
      + false* select_is_term_absurd H1.
      + false* select_is_term_absurd H1.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards* (-> & -> & Heq): select_eq_inv H2. inverts* Heq.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards* (-> & -> & Heq): select_eq_inv H2. inverts* Heq.
    - inverts~ Hmatch2.
      + false* select_is_term_absurd H1.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards* (-> & -> & Heq): select_eq_inv H3. inverts* Heq.
    - inverts~ Hmatch2.
      + false* select_is_term_absurd H1.
      + false* select_is_term_absurd H1.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        inverts Hall3 as Htm Hall3.
        forwards* (-> & -> & Heq): select_eq_inv H1. inverts* Heq.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        inverts Hall3 as Htm Hall3.
        forwards* (-> & -> & Heq): select_eq_inv H1. inverts* Heq.
    - inverts~ Hmatch2.
      + false* select_is_term_absurd H1.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards* (-> & -> & Heq): select_eq_inv H1. inverts* Heq.
    - inverts Hmatch2.
      + false* select_is_term_absurd H0.
      + false* select_is_term_absurd H0.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards~ (-> & -> & ->): select_eq_inv H3.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards~ (-> & -> & ->): select_eq_inv H3.
        forwards* Heq: IHHmatch1. inverts Heq.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards~ (-> & -> & ->): select_eq_inv H3.
    - inverts Hmatch2.
      + false* select_is_term_absurd H0.
      + false* select_is_term_absurd H0.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards~ (-> & -> & ->): select_eq_inv H3.
        forwards* Heq: IHHmatch1_1. inverts Heq.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards~ (-> & -> & ->): select_eq_inv H3.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards~ (-> & -> & ->): select_eq_inv H3.
    - inverts Hmatch2.
      + false* select_is_term_absurd H0.
      + false* select_is_term_absurd H0.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards~ (-> & -> & ->): select_eq_inv H3.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards~ (-> & -> & ->): select_eq_inv H3.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards~ (-> & -> & ->): select_eq_inv H3.
    - inverts Hmatch2.
      + false* select_is_term_absurd H0.
      + false* select_is_term_absurd H0.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards~ (-> & -> & ->): select_eq_inv H3.
        forwards* Heq: IHHmatch1_1. inverts Heq.
        forwards~ Hmtm': match_pattern_preserves_matching_term H4.
        forwards* Heq: IHHmatch1_2.
        {
          introv Hlt Hmtm'' Hmatch'1 Hmatch2'.
          forwards~: match_pattern_preserves_term_size H4.
          applys* IH. nat_math.
        }
        inverts* Heq.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards~ (-> & -> & ->): select_eq_inv H3.
        forwards* Heq: IHHmatch1_1. inverts Heq.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards~ (-> & -> & ->): select_eq_inv H3.
        forwards* Heq: IHHmatch1_1. inverts Heq.
        forwards~ Hmtm': match_pattern_preserves_matching_term H4.
        forwards* Heq: IHHmatch1_2.
        {
          introv Hlt Hmtm'' Hmatch'1 Hmatch2'.
          forwards*: match_pattern_preserves_term_size H4.
          applys* IH. nat_math.
        }
        inverts* Heq.
    - inverts~ Hmatch2.
      + false* select_is_term_absurd H0.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards~ (-> & -> & ->): select_eq_inv H3.
        forwards* Heq: IHHmatch1. inverts Heq.
    - inverts~ Hmatch2.
      + false* select_is_term_absurd H0.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards~ (-> & -> & ->): select_eq_inv H3.
        forwards* Heq: IHHmatch1_1. inverts Heq.
        forwards~ Hmtm': match_pattern_preserves_matching_term H4.
        forwards* Heq: IHHmatch1_2.
        {
          introv Hlt Hmtm'' Hmatch'1 Hmatch2'.
          forwards*: match_pattern_preserves_term_size H4.
          applys* IH. nat_math.
        }
        inverts* Heq.
    - inverts Hmatch2.
      + false* select_is_term_absurd H0.
      + false* select_is_term_absurd H0.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards~ (-> & -> & Heq): select_eq_inv H3. inverts Heq.
        forwards* Heq: IHHmatch1_1. inverts Heq.
        forwards~ Hmtm': match_pattern_preserves_matching_term H4.
        forwards (Hall1' & Hall2' & Hall3'): is_matching_term_select_inv Hmtm'.
        forwards* (Hall21 & Htm): Forall_last_inv.
        inverts Htm.
        forwards* Heq: IHHmatch1_2.
        {
          introv Hlt Hmtm'' Hmatch'1 Hmatch2'.
          forwards~: match_pattern_preserves_term_size H4.
          applys* IH. simpls. folds terms_size.
          rewrite terms_size_app. rewrite terms_size_app in Hlt. simpls.
          rewrite terms_size_app. rewrite terms_size_app in Hlt. simpls.
          folds terms_size. nat_math.
        }
        inverts* Heq.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards~ (-> & -> & <-): select_eq_inv H3.
        forwards* Heq: IHHmatch1_1. inverts Heq.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards~ (-> & -> & <-): select_eq_inv H3.
        forwards* Heq: IHHmatch1_1. inverts Heq.
        forwards~ Hmtm': match_pattern_preserves_matching_term H4.
        forwards (Hall1' & Hall2' & Hall3'): is_matching_term_select_inv Hmtm'.
        forwards* (Hall2'1 & Hall2'2): Forall_app_inv.
        forwards* (_ & Heq & <-): select_eq_inv H0.
        apply app_cancel_l in Heq. subst.
        forwards* Heq: IHHmatch1_2.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        inverts Hall3 as Htm Hall.
        inverts Htm.
        forwards* (-> & -> & Heq): select_eq_inv H3. inverts Heq.
        forwards* Heq: IHHmatch1_1. inverts Heq.
        forwards~ Hmtm': match_pattern_preserves_matching_term H4.
        forwards (Hall1' & Hall2' & Hall3'): is_matching_term_select_inv Hmtm'.
        forwards* (Hall2'1 & Hall2'2): Forall_app_inv.
        inverts Hall2'2 as Htm' _. inverts Htm'.
        forwards* Heq: IHHmatch1_2.
        {
          introv Hlt Hmtm'' Hmatch'1 Hmatch2'.
          forwards~: match_pattern_preserves_term_size H4.
          applys* IH. simpls. folds terms_size.
          rewrite terms_size_app. rewrite terms_size_app in Hlt. simpls.
          rewrite terms_size_app. rewrite terms_size_app in Hlt. simpls.
          folds terms_size. nat_math.
        }
        inverts Heq.
    - inverts~ Hmatch2.
      + false* select_is_term_absurd H0.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards~ (-> & -> & ->): select_eq_inv H3.
        forwards* Heq: IHHmatch1. inverts Heq.
    - inverts~ Hmatch2.
      + false* select_is_term_absurd H1.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards~ (-> & -> & ->): select_eq_inv H4.
        forwards* Heq: IHHmatch1. inverts Heq.
        inverts Hall3 as Htm Hall3.
        inverts Htm.
        forwards* (_ & Heq & <-): select_eq_inv H1.
        apply app_cancel_l in Heq. subst.
        forwards* Heq: IHHmatch1.
    - inverts~ Hmatch2.
      + false* select_is_term_absurd H0.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards~ (-> & -> & Heq): select_eq_inv H3. inverts Heq.
        forwards* Heq: IHHmatch1_1. inverts Heq.
        inverts Hall3 as Htm Hall3.
        inverts Htm.
        forwards* Heq: IHHmatch1_2.
        {
          introv Hlt Hmtm'' Hmatch'1 Hmatch2'.
          forwards~: match_pattern_preserves_term_size H4.
          applys* IH. simpls. folds terms_size.
          rewrite terms_size_app. rewrite terms_size_app in Hlt. simpls.
          rewrite terms_size_app. rewrite terms_size_app in Hlt. simpls.
          folds terms_size. nat_math.
        }
        inverts Heq.
    - inverts Hmatch2.
      + false* select_is_term_absurd H0.
      + false* select_is_term_absurd H0.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards* (-> & -> & Heq): select_eq_inv H2. inverts* Heq.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards* (-> & -> & Heq): select_eq_inv H2. inverts Heq.
        forwards* Heq: IHHmatch1. inverts Heq.
    - inverts Hmatch2.
      + false* select_is_term_absurd H0.
      + false* select_is_term_absurd H0.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards* (-> & -> & Heq): select_eq_inv H2. inverts Heq.
        forwards* Heq: IHHmatch1. inverts Heq.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards* (-> & -> & Heq): select_eq_inv H2.
    - inverts Hmatch2.
      + false* select_is_term_absurd H0.
      + false* select_is_term_absurd H0.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards* (-> & -> & Heq): select_eq_inv H2. inverts Heq.
        forwards* Heq: IHHmatch1.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards* (-> & -> & ->): select_eq_inv H2.
        forwards* Heq: IHHmatch1. inverts Heq.
    - inverts Hmatch2.
      + false* select_is_term_absurd H0.
      + false* select_is_term_absurd H0.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards* (-> & -> & Heq): select_eq_inv H2. inverts Heq.
        forwards* Heq: IHHmatch1. inverts Heq.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards* (-> & -> & ->): select_eq_inv H2.
    - inverts Hmatch2.
      + false* select_is_term_absurd H1.
      + false* select_is_term_absurd H1.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards* (-> & -> & ->): select_eq_inv H2.
        forwards* Heq: IHHmatch1_1. inverts Heq.
        forwards~ Hmtm': match_pattern_preserves_matching_term H3.
        forwards (Hall1' & Hall2' & Hall3'): is_matching_term_select_inv Hmtm'.
        forwards* (Hall2'1 & Hall2'2): Forall_app_inv.
        forwards* (_ & Heq & ->): select_eq_inv H1.
        apply app_cancel_l in Heq. subst.
        forwards* Heq: IHHmatch1_2.
        {
          introv Hlt Hmtm'' Hmatch'1 Hmatch2'.
          folds terms_size.
          forwards~ Heq: match_pattern_preserves_term_size H3.
          apply* IH. simpls. folds terms_size. inverts Heq.
          rewrite H5. nat_math.
        }
        inverts* Heq.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards* (-> & -> & ->): select_eq_inv H3.
        forwards* Heq: IHHmatch1_1. inverts Heq.
    - inverts Hmatch2.
      + false* select_is_term_absurd H1.
      + false* select_is_term_absurd H1.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards* (-> & -> & ->): select_eq_inv H1.
        forwards* Heq: IHHmatch1. inverts Heq.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards* (-> & -> & ->): select_eq_inv H2.
    - inverts Hmatch2.
      + false* select_is_term_absurd H1.
      + false* select_is_term_absurd H1.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards* (-> & -> & ->): select_eq_inv H4.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards* (-> & -> & ->): select_eq_inv H4.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards* (-> & -> & ->): select_eq_inv H4.
        forwards~ Hmtm': match_pattern_preserves_matching_term H5.
        forwards (Hall1' & Hall2' & Hall3'): is_matching_term_select_inv Hmtm'.
        forwards* (Hall2'1 & Hall2'2): Forall_app_inv.
        forwards* Heq: IHHmatch1. inverts Heq as Heq.
        forwards* (_ & Heq' & ->): select_eq_inv Heq.
        apply app_cancel_l in Heq'. subst.
        false*.
    - inverts~ Hmatch2.
      + false* select_is_term_absurd H1.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards* (-> & -> & ->): select_eq_inv H3.
    - inverts~ Hmatch2.
      + false* select_is_term_absurd H1.
      + forwards (Hall1 & Hall2 & Hall3): is_matching_term_select_inv Hmtm.
        forwards* (-> & -> & ->): select_eq_inv H4.
        forwards~ Hmtm': match_pattern_preserves_matching_term H5.
        forwards (Hall1' & Hall2' & Hall3'): is_matching_term_select_inv Hmtm'.
        forwards* (Hall2'1 & Hall2'2): Forall_app_inv.
        forwards* Heq: IHHmatch1. inverts Heq as Heq.
        forwards* (_ & Heq' & ->): select_eq_inv Heq.
        apply app_cancel_l in Heq'. subst.
        false*.
  Qed.

  (* TODO: Can we prove completeness? It seems to be needed for
  making the below an equivalence *)
  Lemma nomatch_is_negation:
    forall p tm tm' M,
      is_matching_term tm ->
      match_pattern p tm None ->
      ~match_pattern p tm (Some (tm', M)).
  Proof using.
    introv Hmtm Hnmatch contra.
    forwards* absurd: match_pattern_deterministic Hnmatch contra.
    inverts absurd.
  Qed.

  (* TODO: Something makes automation slow... *)

  (* NO MORE FUN UNTIL OOPSLA PAPER IS DONE! *)

End Trieste.