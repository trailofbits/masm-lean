import MidenLean.Proofs.Sha256.PrepareMessageScheduleAndConsume.SBs0to7

namespace MidenLean.Proofs.Sha256

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics


private lemma sha256SB8Ops_split :
    sha256SB8Ops = sha256RegularExpandOps ++ sha256RegularConsumeOps 666307205 773529912 1294757372 1396182291 := by
  simp only [sha256RegularExpandOps, sha256RegularConsumeOps, sha256SB8Ops, sha256BodyOps]
  set_option maxRecDepth 4096 in rfl

private lemma sha256SB9Ops_split :
    sha256SB9Ops = sha256RegularExpandOps ++ sha256RegularConsumeOps 1695183700 1986661051 2177026350 2456956037 := by
  simp only [sha256RegularExpandOps, sha256RegularConsumeOps, sha256SB9Ops, sha256BodyOps]
  set_option maxRecDepth 4096 in rfl

private lemma sha256SB10Ops_split :
    sha256SB10Ops = sha256RegularExpandOps ++ sha256RegularConsumeOps 2730485921 2820302411 3259730800 3345764771 := by
  simp only [sha256RegularExpandOps, sha256RegularConsumeOps, sha256SB10Ops, sha256BodyOps]
  set_option maxRecDepth 4096 in rfl

private lemma sha256SB11Ops_split :
    sha256SB11Ops = sha256RegularExpandOps ++ sha256RegularConsumeOps 3516065817 3600352804 4094571909 275423344 := by
  simp only [sha256RegularExpandOps, sha256RegularConsumeOps, sha256SB11Ops, sha256BodyOps]
  set_option maxRecDepth 4096 in rfl

-- SB8: Input = SB7 output = [W47,W46,W45,W44, W35,W34,W33,W32, W43,W42,W41,W40, W39,W38,W37,W36]
-- a=[W47..W44], b=[W35..W32], c=[W43..W40], d=[W39..W36]
-- new1 = sha256W W46 W41 W33 W32 (= W48)
-- new2 = sha256W W47 W42 W34 W33 (= W49)
-- new3 = sha256W W48 W43 W35 W34 (= W50)
-- new4 = sha256W W49 W44 W36 W35 (= W51)
-- Consumed: [W32,W33,W34,W35] with K[32..35]
-- Output: [W51,W50,W49,W48, W39,W38,W37,W36, W47,W46,W45,W44, W43,W42,W41,W40]

set_option maxHeartbeats 800000 in
lemma sha256_SB8_bridge
    (W47 W46 W45 W44 W35 W34 W33 W32 W43 W42 W41 W40 W39 W38 W37 W36 : Felt)
    (a b c d e f g h : Felt)
    (H0 H1 H2 H3 H4 H5 H6 H7 : Felt)
    (hW47 : W47.isU32 = true) (hW46 : W46.isU32 = true)
    (_hW45 : W45.isU32 = true) (hW44 : W44.isU32 = true)
    (hW35 : W35.isU32 = true) (hW34 : W34.isU32 = true)
    (hW33 : W33.isU32 = true) (hW32 : W32.isU32 = true)
    (hW43 : W43.isU32 = true) (hW42 : W42.isU32 = true)
    (hW41 : W41.isU32 = true) (_hW40 : W40.isU32 = true)
    (hW36 : W36.isU32 = true) (_hW37 : W37.isU32 = true)
    (_hW38 : W38.isU32 = true) (_hW39 : W39.isU32 = true)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hc : c.isU32 = true) (hd : d.isU32 = true)
    (he : e.isU32 = true) (hf : f.isU32 = true) (hg : g.isU32 = true) (hh : h.isU32 = true)
    (_hH0 : H0.isU32 = true) (_hH1 : H1.isU32 = true) (_hH2 : H2.isU32 = true)
    (_hH3 : H3.isU32 = true) (_hH4 : H4.isU32 = true) (_hH5 : H5.isU32 = true)
    (_hH6 : H6.isU32 = true) (_hH7 : H7.isU32 = true)
    (rest : List Felt) (mem locs : Nat → Felt) (adv : List Felt)
    (base : Nat → Felt)
    (hlocs : locs = sha256WorkingLocs a b c d e f g h H0 H1 H2 H3 H4 H5 H6 H7 base) :
    let W48 := sha256W W46 W41 W33 W32
    let W49 := sha256W W47 W42 W34 W33
    let W50 := sha256W W48 W43 W35 W34
    let W51 := sha256W W49 W44 W36 W35
    let (na, nb, nc, nd, ne, nf, ng, nh) := sha256Compress4 a b c d e f g h W32 W33 W34 W35 666307205 773529912 1294757372 1396182291
    execWithEnv sha256ProcEnv 2126
        ⟨W47::W46::W45::W44::W35::W34::W33::W32::W43::W42::W41::W40::W39::W38::W37::W36::rest,
          mem, locs, adv⟩
        sha256SB8Ops =
    some ⟨W51 :: W50 :: W49 :: W48 :: W39 :: W38 :: W37 :: W36 ::
          W47 :: W46 :: W45 :: W44 :: W43 :: W42 :: W41 :: W40 :: rest,
          mem,
          sha256WorkingLocs na nb nc nd ne nf ng nh H0 H1 H2 H3 H4 H5 H6 H7 base,
          adv⟩ := by
  rw [sha256SB8Ops_split, execWithEnv_append]
  rw [sha256_regular_expand_bridge W47 W46 W45 W44 W35 W34 W33 W32 W43 W42 W41 W40 W39 W38 W37 W36
      hW47 hW46 hW44 hW35 hW34 hW33 hW32 hW43 hW42 hW41 hW36 rest mem locs adv]
  simp only [bind, Bind.bind, Option.bind]
  rw [sha256_regular_consume_bridge W32 W33 W34 W35
      (sha256W (sha256W W47 W42 W34 W33) W44 W36 W35)
      (sha256W (sha256W W46 W41 W33 W32) W43 W35 W34)
      (sha256W W47 W42 W34 W33) (sha256W W46 W41 W33 W32)
      W39 W38 W37 W36 W47 W46 W45 W44 W43 W42 W41 W40
      a b c d e f g h H0 H1 H2 H3 H4 H5 H6 H7
      666307205 773529912 1294757372 1396182291
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hW32 hW33 hW34 hW35 ha hb hc hd he hf hg hh
      rest mem locs adv base hlocs]
  dsimp only [sha256Compress4, consumeResult, sha256W]

-- SB9: Input = SB8 output = [W51,W50,W49,W48, W39,W38,W37,W36, W47,W46,W45,W44, W43,W42,W41,W40]
-- a=[W51..W48], b=[W39..W36], c=[W47..W44], d=[W43..W40]
-- new1 = sha256W W50 W45 W37 W36 (= W52)
-- new2 = sha256W W51 W46 W38 W37 (= W53)
-- new3 = sha256W W52 W47 W39 W38 (= W54)
-- new4 = sha256W W53 W48 W40 W39 (= W55)
-- Consumed: [W36,W37,W38,W39] with K[36..39]
-- Output: [W55,W54,W53,W52, W43,W42,W41,W40, W51,W50,W49,W48, W47,W46,W45,W44]

set_option maxHeartbeats 800000 in
lemma sha256_SB9_bridge
    (W51 W50 W49 W48 W39 W38 W37 W36 W47 W46 W45 W44 W43 W42 W41 W40 : Felt)
    (a b c d e f g h : Felt)
    (H0 H1 H2 H3 H4 H5 H6 H7 : Felt)
    (hW51 : W51.isU32 = true) (hW50 : W50.isU32 = true)
    (_hW49 : W49.isU32 = true) (hW48 : W48.isU32 = true)
    (hW39 : W39.isU32 = true) (hW38 : W38.isU32 = true)
    (hW37 : W37.isU32 = true) (hW36 : W36.isU32 = true)
    (hW47 : W47.isU32 = true) (hW46 : W46.isU32 = true)
    (hW45 : W45.isU32 = true) (_hW44 : W44.isU32 = true)
    (hW40 : W40.isU32 = true) (_hW41 : W41.isU32 = true)
    (_hW42 : W42.isU32 = true) (_hW43 : W43.isU32 = true)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hc : c.isU32 = true) (hd : d.isU32 = true)
    (he : e.isU32 = true) (hf : f.isU32 = true) (hg : g.isU32 = true) (hh : h.isU32 = true)
    (_hH0 : H0.isU32 = true) (_hH1 : H1.isU32 = true) (_hH2 : H2.isU32 = true)
    (_hH3 : H3.isU32 = true) (_hH4 : H4.isU32 = true) (_hH5 : H5.isU32 = true)
    (_hH6 : H6.isU32 = true) (_hH7 : H7.isU32 = true)
    (rest : List Felt) (mem locs : Nat → Felt) (adv : List Felt)
    (base : Nat → Felt)
    (hlocs : locs = sha256WorkingLocs a b c d e f g h H0 H1 H2 H3 H4 H5 H6 H7 base) :
    let W52 := sha256W W50 W45 W37 W36
    let W53 := sha256W W51 W46 W38 W37
    let W54 := sha256W W52 W47 W39 W38
    let W55 := sha256W W53 W48 W40 W39
    let (na, nb, nc, nd, ne, nf, ng, nh) := sha256Compress4 a b c d e f g h W36 W37 W38 W39 1695183700 1986661051 2177026350 2456956037
    execWithEnv sha256ProcEnv 2126
        ⟨W51::W50::W49::W48::W39::W38::W37::W36::W47::W46::W45::W44::W43::W42::W41::W40::rest,
          mem, locs, adv⟩
        sha256SB9Ops =
    some ⟨W55 :: W54 :: W53 :: W52 :: W43 :: W42 :: W41 :: W40 ::
          W51 :: W50 :: W49 :: W48 :: W47 :: W46 :: W45 :: W44 :: rest,
          mem,
          sha256WorkingLocs na nb nc nd ne nf ng nh H0 H1 H2 H3 H4 H5 H6 H7 base,
          adv⟩ := by
  rw [sha256SB9Ops_split, execWithEnv_append]
  rw [sha256_regular_expand_bridge W51 W50 W49 W48 W39 W38 W37 W36 W47 W46 W45 W44 W43 W42 W41 W40
      hW51 hW50 hW48 hW39 hW38 hW37 hW36 hW47 hW46 hW45 hW40 rest mem locs adv]
  simp only [bind, Bind.bind, Option.bind]
  rw [sha256_regular_consume_bridge W36 W37 W38 W39
      (sha256W (sha256W W51 W46 W38 W37) W48 W40 W39)
      (sha256W (sha256W W50 W45 W37 W36) W47 W39 W38)
      (sha256W W51 W46 W38 W37) (sha256W W50 W45 W37 W36)
      W43 W42 W41 W40 W51 W50 W49 W48 W47 W46 W45 W44
      a b c d e f g h H0 H1 H2 H3 H4 H5 H6 H7
      1695183700 1986661051 2177026350 2456956037
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hW36 hW37 hW38 hW39 ha hb hc hd he hf hg hh
      rest mem locs adv base hlocs]
  dsimp only [sha256Compress4, consumeResult, sha256W]

-- SB10: Input = SB9 output = [W55,W54,W53,W52, W43,W42,W41,W40, W51,W50,W49,W48, W47,W46,W45,W44]
-- a=[W55..W52], b=[W43..W40], c=[W51..W48], d=[W47..W44]
-- new1 = sha256W W54 W49 W41 W40 (= W56)
-- new2 = sha256W W55 W50 W42 W41 (= W57)
-- new3 = sha256W W56 W51 W43 W42 (= W58)
-- new4 = sha256W W57 W52 W44 W43 (= W59)
-- Consumed: [W40,W41,W42,W43] with K[40..43]
-- Output: [W59,W58,W57,W56, W47,W46,W45,W44, W55,W54,W53,W52, W51,W50,W49,W48]

set_option maxHeartbeats 800000 in
lemma sha256_SB10_bridge
    (W55 W54 W53 W52 W43 W42 W41 W40 W51 W50 W49 W48 W47 W46 W45 W44 : Felt)
    (a b c d e f g h : Felt)
    (H0 H1 H2 H3 H4 H5 H6 H7 : Felt)
    (hW55 : W55.isU32 = true) (hW54 : W54.isU32 = true)
    (_hW53 : W53.isU32 = true) (hW52 : W52.isU32 = true)
    (hW43 : W43.isU32 = true) (hW42 : W42.isU32 = true)
    (hW41 : W41.isU32 = true) (hW40 : W40.isU32 = true)
    (hW51 : W51.isU32 = true) (hW50 : W50.isU32 = true)
    (hW49 : W49.isU32 = true) (_hW48 : W48.isU32 = true)
    (hW44 : W44.isU32 = true) (_hW45 : W45.isU32 = true)
    (_hW46 : W46.isU32 = true) (_hW47 : W47.isU32 = true)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hc : c.isU32 = true) (hd : d.isU32 = true)
    (he : e.isU32 = true) (hf : f.isU32 = true) (hg : g.isU32 = true) (hh : h.isU32 = true)
    (_hH0 : H0.isU32 = true) (_hH1 : H1.isU32 = true) (_hH2 : H2.isU32 = true)
    (_hH3 : H3.isU32 = true) (_hH4 : H4.isU32 = true) (_hH5 : H5.isU32 = true)
    (_hH6 : H6.isU32 = true) (_hH7 : H7.isU32 = true)
    (rest : List Felt) (mem locs : Nat → Felt) (adv : List Felt)
    (base : Nat → Felt)
    (hlocs : locs = sha256WorkingLocs a b c d e f g h H0 H1 H2 H3 H4 H5 H6 H7 base) :
    let W56 := sha256W W54 W49 W41 W40
    let W57 := sha256W W55 W50 W42 W41
    let W58 := sha256W W56 W51 W43 W42
    let W59 := sha256W W57 W52 W44 W43
    let (na, nb, nc, nd, ne, nf, ng, nh) := sha256Compress4 a b c d e f g h W40 W41 W42 W43 2730485921 2820302411 3259730800 3345764771
    execWithEnv sha256ProcEnv 2126
        ⟨W55::W54::W53::W52::W43::W42::W41::W40::W51::W50::W49::W48::W47::W46::W45::W44::rest,
          mem, locs, adv⟩
        sha256SB10Ops =
    some ⟨W59 :: W58 :: W57 :: W56 :: W47 :: W46 :: W45 :: W44 ::
          W55 :: W54 :: W53 :: W52 :: W51 :: W50 :: W49 :: W48 :: rest,
          mem,
          sha256WorkingLocs na nb nc nd ne nf ng nh H0 H1 H2 H3 H4 H5 H6 H7 base,
          adv⟩ := by
  rw [sha256SB10Ops_split, execWithEnv_append]
  rw [sha256_regular_expand_bridge W55 W54 W53 W52 W43 W42 W41 W40 W51 W50 W49 W48 W47 W46 W45 W44
      hW55 hW54 hW52 hW43 hW42 hW41 hW40 hW51 hW50 hW49 hW44 rest mem locs adv]
  simp only [bind, Bind.bind, Option.bind]
  rw [sha256_regular_consume_bridge W40 W41 W42 W43
      (sha256W (sha256W W55 W50 W42 W41) W52 W44 W43)
      (sha256W (sha256W W54 W49 W41 W40) W51 W43 W42)
      (sha256W W55 W50 W42 W41) (sha256W W54 W49 W41 W40)
      W47 W46 W45 W44 W55 W54 W53 W52 W51 W50 W49 W48
      a b c d e f g h H0 H1 H2 H3 H4 H5 H6 H7
      2730485921 2820302411 3259730800 3345764771
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hW40 hW41 hW42 hW43 ha hb hc hd he hf hg hh
      rest mem locs adv base hlocs]
  dsimp only [sha256Compress4, consumeResult, sha256W]

-- SB11: Input = SB10 output = [W59,W58,W57,W56, W47,W46,W45,W44, W55,W54,W53,W52, W51,W50,W49,W48]
-- a=[W59..W56], b=[W47..W44], c=[W55..W52], d=[W51..W48]
-- new1 = sha256W W58 W53 W45 W44 (= W60)
-- new2 = sha256W W59 W54 W46 W45 (= W61)
-- new3 = sha256W W60 W55 W47 W46 (= W62)
-- new4 = sha256W W61 W56 W48 W47 (= W63)
-- Consumed: [W44,W45,W46,W47] with K[44..47]
-- Output: [W63,W62,W61,W60, W51,W50,W49,W48, W59,W58,W57,W56, W55,W54,W53,W52]

set_option maxHeartbeats 800000 in
lemma sha256_SB11_bridge
    (W59 W58 W57 W56 W47 W46 W45 W44 W55 W54 W53 W52 W51 W50 W49 W48 : Felt)
    (a b c d e f g h : Felt)
    (H0 H1 H2 H3 H4 H5 H6 H7 : Felt)
    (hW59 : W59.isU32 = true) (hW58 : W58.isU32 = true)
    (_hW57 : W57.isU32 = true) (hW56 : W56.isU32 = true)
    (hW47 : W47.isU32 = true) (hW46 : W46.isU32 = true)
    (hW45 : W45.isU32 = true) (hW44 : W44.isU32 = true)
    (hW55 : W55.isU32 = true) (hW54 : W54.isU32 = true)
    (hW53 : W53.isU32 = true) (_hW52 : W52.isU32 = true)
    (hW48 : W48.isU32 = true) (_hW49 : W49.isU32 = true)
    (_hW50 : W50.isU32 = true) (_hW51 : W51.isU32 = true)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hc : c.isU32 = true) (hd : d.isU32 = true)
    (he : e.isU32 = true) (hf : f.isU32 = true) (hg : g.isU32 = true) (hh : h.isU32 = true)
    (_hH0 : H0.isU32 = true) (_hH1 : H1.isU32 = true) (_hH2 : H2.isU32 = true)
    (_hH3 : H3.isU32 = true) (_hH4 : H4.isU32 = true) (_hH5 : H5.isU32 = true)
    (_hH6 : H6.isU32 = true) (_hH7 : H7.isU32 = true)
    (rest : List Felt) (mem locs : Nat → Felt) (adv : List Felt)
    (base : Nat → Felt)
    (hlocs : locs = sha256WorkingLocs a b c d e f g h H0 H1 H2 H3 H4 H5 H6 H7 base) :
    let W60 := sha256W W58 W53 W45 W44
    let W61 := sha256W W59 W54 W46 W45
    let W62 := sha256W W60 W55 W47 W46
    let W63 := sha256W W61 W56 W48 W47
    let (na, nb, nc, nd, ne, nf, ng, nh) := sha256Compress4 a b c d e f g h W44 W45 W46 W47 3516065817 3600352804 4094571909 275423344
    execWithEnv sha256ProcEnv 2126
        ⟨W59::W58::W57::W56::W47::W46::W45::W44::W55::W54::W53::W52::W51::W50::W49::W48::rest,
          mem, locs, adv⟩
        sha256SB11Ops =
    some ⟨W63 :: W62 :: W61 :: W60 :: W51 :: W50 :: W49 :: W48 ::
          W59 :: W58 :: W57 :: W56 :: W55 :: W54 :: W53 :: W52 :: rest,
          mem,
          sha256WorkingLocs na nb nc nd ne nf ng nh H0 H1 H2 H3 H4 H5 H6 H7 base,
          adv⟩ := by
  rw [sha256SB11Ops_split, execWithEnv_append]
  rw [sha256_regular_expand_bridge W59 W58 W57 W56 W47 W46 W45 W44 W55 W54 W53 W52 W51 W50 W49 W48
      hW59 hW58 hW56 hW47 hW46 hW45 hW44 hW55 hW54 hW53 hW48 rest mem locs adv]
  simp only [bind, Bind.bind, Option.bind]
  rw [sha256_regular_consume_bridge W44 W45 W46 W47
      (sha256W (sha256W W59 W54 W46 W45) W56 W48 W47)
      (sha256W (sha256W W58 W53 W45 W44) W55 W47 W46)
      (sha256W W59 W54 W46 W45) (sha256W W58 W53 W45 W44)
      W51 W50 W49 W48 W59 W58 W57 W56 W55 W54 W53 W52
      a b c d e f g h H0 H1 H2 H3 H4 H5 H6 H7
      3516065817 3600352804 4094571909 275423344
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hW44 hW45 hW46 hW47 ha hb hc hd he hf hg hh
      rest mem locs adv base hlocs]
  dsimp only [sha256Compress4, consumeResult, sha256W]



-- ============================================================================
-- SB12 bridge lemma
-- SB12 is the first compression-only block (no message schedule expansion).
-- It loads the compression state from locs, consumes W48..W51 with K[48..51],
-- then rearranges the stack for the next SB.
-- Input:  [W63,W62,W61,W60, W51,W50,W49,W48, W59,W58,W57,W56, W55,W54,W53,W52, rest]
-- Output: [na,..,nh, W52,W53,W54,W55, W59,W58,W57,W56, W63,W62,W61,W60, rest]
--   with locs UNCHANGED (no locStore at end)
-- ============================================================================

-- Split SB12 into rearrange + load/consume + rearrange
private def sha256SB12RearrangeOps : List Op := [
    .inst (.movupw 2), .inst (.movupw 3), .inst (.movupw 3),
    .inst (.exec "rev_element_order")]

private def sha256SB12ConsumeOps : List Op := [
    .inst (.push 430227734), .inst .padw, .inst (.locLoadwBe 4),
    .inst .padw, .inst (.locLoadwBe 0),
    .inst (.exec "consume_message_word"),
    .inst (.push 506948616), .inst (.movdn 8),
    .inst (.exec "consume_message_word"),
    .inst (.push 659060556), .inst (.movdn 8),
    .inst (.exec "consume_message_word"),
    .inst (.push 883997877), .inst (.movdn 8),
    .inst (.exec "consume_message_word")]

private def sha256SB12TrailingOps : List Op := [
    .inst (.movupw 2), .inst (.exec "rev_element_order"), .inst (.movdnw 2)]

private lemma sha256SB12Ops_split :
    sha256SB12Ops = sha256SB12RearrangeOps ++ sha256SB12ConsumeOps ++ sha256SB12TrailingOps := by
  simp only [sha256SB12RearrangeOps, sha256SB12ConsumeOps, sha256SB12TrailingOps,
             sha256SB12Ops, sha256BodyOps]
  set_option maxRecDepth 4096 in rfl

-- SB13/14/15 consume ops (no locLoad, no locStore, just push+movdn+consume x4 + trailing rearrange)
private def sha256SB13ConsumeOps : List Op := [
    .inst (.push 958139571), .inst (.movdn 8),
    .inst (.exec "consume_message_word"),
    .inst (.push 1322822218), .inst (.movdn 8),
    .inst (.exec "consume_message_word"),
    .inst (.push 1537002063), .inst (.movdn 8),
    .inst (.exec "consume_message_word"),
    .inst (.push 1747873779), .inst (.movdn 8),
    .inst (.exec "consume_message_word")]

private def sha256SB13TrailingOps : List Op := [
    .inst (.movupw 2), .inst (.exec "rev_element_order"), .inst (.movdnw 2)]

private lemma sha256SB13Ops_split :
    sha256SB13Ops = sha256SB13ConsumeOps ++ sha256SB13TrailingOps := by
  simp only [sha256SB13ConsumeOps, sha256SB13TrailingOps, sha256SB13Ops, sha256BodyOps]
  set_option maxRecDepth 4096 in rfl

private def sha256SB14ConsumeOps : List Op := [
    .inst (.push 1955562222), .inst (.movdn 8),
    .inst (.exec "consume_message_word"),
    .inst (.push 2024104815), .inst (.movdn 8),
    .inst (.exec "consume_message_word"),
    .inst (.push 2227730452), .inst (.movdn 8),
    .inst (.exec "consume_message_word"),
    .inst (.push 2361852424), .inst (.movdn 8),
    .inst (.exec "consume_message_word")]

private def sha256SB14TrailingOps : List Op := [
    .inst (.movupw 2), .inst (.exec "rev_element_order"), .inst (.movdnw 2)]

private lemma sha256SB14Ops_split :
    sha256SB14Ops = sha256SB14ConsumeOps ++ sha256SB14TrailingOps := by
  simp only [sha256SB14ConsumeOps, sha256SB14TrailingOps, sha256SB14Ops, sha256BodyOps]
  set_option maxRecDepth 4096 in rfl

-- SB15 has no trailing rearrange (it's the last SB)
private lemma sha256SB15Ops_eq :
    sha256SB15Ops = [
    .inst (.push 2428436474), .inst (.movdn 8),
    .inst (.exec "consume_message_word"),
    .inst (.push 2756734187), .inst (.movdn 8),
    .inst (.exec "consume_message_word"),
    .inst (.push 3204031479), .inst (.movdn 8),
    .inst (.exec "consume_message_word"),
    .inst (.push 3329325298), .inst (.movdn 8),
    .inst (.exec "consume_message_word")] := by
  simp only [sha256SB15Ops, sha256BodyOps]
  set_option maxRecDepth 4096 in rfl


-- ============================================================================

               if_neg (show i ≠ 1 from by omega), if_neg (show i ≠ 0 from by omega)]

-- ============================================================================
-- Generic "stack-only consume" bridge lemma
-- Consumes 4 message words from positions 8–11 of the stack (after push+movdn).
-- No locLoad/locStore — compression state is passed directly on the stack.
-- Input:  [a,b,c,d,e,f,g,h, w0,w1,w2,w3, rest...]
-- Output: [na,..,nh, rest...]
-- ============================================================================

set_option maxHeartbeats 4000000 in
lemma sha256_stack_consume4_bridge
    (a b c d e f g h w0 w1 w2 w3 : Felt) (rest : List Felt)
    (k0 k1 k2 k3 : Nat)
    (hk0 : k0 < 2^32) (hk1 : k1 < 2^32) (hk2 : k2 < 2^32) (hk3 : k3 < 2^32)
    (hw0 : w0.isU32 = true) (hw1 : w1.isU32 = true) (hw2 : w2.isU32 = true)
    (hw3 : w3.isU32 = true)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hc : c.isU32 = true) (hd : d.isU32 = true)
    (he : e.isU32 = true) (hf : f.isU32 = true) (hg : g.isU32 = true) (hh : h.isU32 = true)
    (mem locs : Nat → Felt) (adv : List Felt) :
    let (na, nb, nc, nd, ne, nf, ng, nh) := sha256Compress4 a b c d e f g h w0 w1 w2 w3 k0 k1 k2 k3
    execWithEnv sha256ProcEnv 2126
        ⟨a :: b :: c :: d :: e :: f :: g :: h :: w0 :: w1 :: w2 :: w3 :: rest,
          mem, locs, adv⟩
        [.inst (.push k0), .inst (.movdn 8),
         .inst (.exec "consume_message_word"),
         .inst (.push k1), .inst (.movdn 8),
         .inst (.exec "consume_message_word"),
         .inst (.push k2), .inst (.movdn 8),
         .inst (.exec "consume_message_word"),
         .inst (.push k3), .inst (.movdn 8),
         .inst (.exec "consume_message_word")] =
    some ⟨na :: nb :: nc :: nd :: ne :: nf :: ng :: nh :: rest,
          mem, locs, adv⟩ := by
  unfold execWithEnv; simp only [List.foldlM]
  rw [stepPush]; miden_bind
  rw [stepMovdn (hn := rfl)]; miden_bind
  simp only [show sha256ProcEnv "consume_message_word" =
      some Miden.Core.Sha256.consume_message_word from rfl]
  rw [consume_message_word_at_2125 a b c d e f g h (Felt.ofNat k0) w0
      _ _ rfl ha hb hc hd he hf hg hh (felt_ofNat_isU32_of_lt _ hk0) hw0]
  simp only [MidenState.withStack]
  rw [stepPush]; miden_bind
  rw [stepMovdn (hn := rfl)]; miden_bind
  rw [consume_message_word_at_2125 _ _ _ _ _ _ _ _ (Felt.ofNat k1) w1
      _ _ rfl (u32_mod_isU32 _) ha hb hc (u32_mod_isU32 _) he hf hg
      (felt_ofNat_isU32_of_lt _ hk1) hw1]
  simp only [MidenState.withStack]
  rw [stepPush]; miden_bind
  rw [stepMovdn (hn := rfl)]; miden_bind
  rw [consume_message_word_at_2125 _ _ _ _ _ _ _ _ (Felt.ofNat k2) w2
      _ _ rfl (u32_mod_isU32 _) (u32_mod_isU32 _) ha hb (u32_mod_isU32 _) (u32_mod_isU32 _)
      he hf (felt_ofNat_isU32_of_lt _ hk2) hw2]
  simp only [MidenState.withStack]
  rw [stepPush]; miden_bind
  rw [stepMovdn (hn := rfl)]; miden_bind
  rw [consume_message_word_at_2125 _ _ _ _ _ _ _ _ (Felt.ofNat k3) w3
      _ _ rfl (u32_mod_isU32 _) (u32_mod_isU32 _) (u32_mod_isU32 _) ha (u32_mod_isU32 _)
      (u32_mod_isU32 _) (u32_mod_isU32 _) he (felt_ofNat_isU32_of_lt _ hk3) hw3]
  simp only [MidenState.withStack]
  dsimp only [pure, Pure.pure]
  simp only [sha256Compress4, consumeResult]

-- ============================================================================
-- Trailing rearrange bridge: movupw 2 + rev_element_order + movdnw 2
-- Takes compression state [a..h] on top with message words below,
-- reverses the word at positions 8–11 and moves it behind the state.
-- Input:  [a,b,c,d, e,f,g,h, x3,x2,x1,x0, rest...]
-- Output: [a,b,c,d, e,f,g,h, x0,x1,x2,x3, rest...]
-- (The movupw2 + rev + movdnw2 reverses the ordering of the 3rd word-group)
-- ============================================================================

lemma sha256_trailing_rearrange_bridge
    (a b c d e f g h x0 x1 x2 x3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt) :
    execWithEnv sha256ProcEnv 2126
        ⟨a :: b :: c :: d :: e :: f :: g :: h :: x0 :: x1 :: x2 :: x3 :: rest,
          mem, locs, adv⟩
        [.inst (.movupw 2), .inst (.exec "rev_element_order"), .inst (.movdnw 2)] =
    some ⟨a :: b :: c :: d :: e :: f :: g :: h :: x3 :: x2 :: x1 :: x0 :: rest,
          mem, locs, adv⟩ := by
  unfold execWithEnv; simp only [List.foldlM]
  rw [stepMovupw2]; miden_bind
  simp only [show sha256ProcEnv "rev_element_order" =
      some Miden.Core.Sha256.rev_element_order from rfl]
  rw [rev_element_order_at_2125 x0 x1 x2 x3
      (a :: b :: c :: d :: e :: f :: g :: h :: rest) mem locs adv]
  simp only [bind, Bind.bind, Option.bind]

-- SB12 bridge
-- ============================================================================

set_option maxHeartbeats 8000000 in
lemma sha256_SB12_bridge
    (W63 W62 W61 W60 W51 W50 W49 W48 W59 W58 W57 W56 W55 W54 W53 W52 : Felt)
    (a b c d e f g h : Felt)
    (H0 H1 H2 H3 H4 H5 H6 H7 : Felt)
    (hW48 : W48.isU32 = true) (hW49 : W49.isU32 = true)
    (hW50 : W50.isU32 = true) (hW51 : W51.isU32 = true)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hc : c.isU32 = true) (hd : d.isU32 = true)
    (he : e.isU32 = true) (hf : f.isU32 = true) (hg : g.isU32 = true) (hh : h.isU32 = true)
    (_hH0 : H0.isU32 = true) (_hH1 : H1.isU32 = true) (_hH2 : H2.isU32 = true)
    (_hH3 : H3.isU32 = true) (_hH4 : H4.isU32 = true) (_hH5 : H5.isU32 = true)
    (_hH6 : H6.isU32 = true) (_hH7 : H7.isU32 = true)
    (rest : List Felt) (mem locs : Nat → Felt) (adv : List Felt)
    (base : Nat → Felt)
    (hlocs : locs = sha256WorkingLocs a b c d e f g h H0 H1 H2 H3 H4 H5 H6 H7 base) :
    let (na, nb, nc, nd, ne, nf, ng, nh) :=
      sha256Compress4 a b c d e f g h W48 W49 W50 W51 430227734 506948616 659060556 883997877
    execWithEnv sha256ProcEnv 2126
        ⟨W63::W62::W61::W60::W51::W50::W49::W48::W59::W58::W57::W56::W55::W54::W53::W52::rest,
          mem, locs, adv⟩
        sha256SB12Ops =
    some ⟨na :: nb :: nc :: nd :: ne :: nf :: ng :: nh ::
          W52 :: W53 :: W54 :: W55 :: W59 :: W58 :: W57 :: W56 :: W63 :: W62 :: W61 :: W60 :: rest,
          mem, locs, adv⟩ := by
  rw [sha256SB12Ops_split, List.append_assoc, execWithEnv_append]
  -- Part A: rearrange [movupw 2, movupw 3, movupw 3, rev_element_order]
  -- Input: [W63,W62,W61,W60, W51,W50,W49,W48, W59,W58,W57,W56, W55,W54,W53,W52, rest]
  -- After movupw 2: [W59,W58,W57,W56, W63,W62,W61,W60, W51,W50,W49,W48, W55,W54,W53,W52, rest]
  -- After movupw 3: [W55,W54,W53,W52, W59,W58,W57,W56, W63,W62,W61,W60, W51,W50,W49,W48, rest]
  -- After movupw 3: [W51,W50,W49,W48, W55,W54,W53,W52, W59,W58,W57,W56, W63,W62,W61,W60, rest]
  -- After rev:       [W48,W49,W50,W51, W55,W54,W53,W52, W59,W58,W57,W56, W63,W62,W61,W60, rest]
  unfold sha256SB12RearrangeOps execWithEnv; simp only [List.foldlM]
  rw [stepMovupw2]; miden_bind
  rw [stepMovupw3]; miden_bind
  rw [stepMovupw3]; miden_bind
  simp only [show sha256ProcEnv "rev_element_order" =
      some Miden.Core.Sha256.rev_element_order from rfl]
  rw [rev_element_order_at_2125 W51 W50 W49 W48
      (W55::W54::W53::W52::W59::W58::W57::W56::W63::W62::W61::W60::rest) mem locs adv]
  simp only [bind, Bind.bind, Option.bind]
  -- Part B: load state from locs + 4 consume rounds
  rw [execWithEnv_append]
  subst hlocs
  simp only [sha256SB12ConsumeOps]
  unfold execWithEnv; simp only [List.foldlM]
  rw [stepPush]; miden_bind
  rw [stepPadw]; miden_bind
  rw [stepLocLoadwBe 4 e f g h
      (h0 := by simp [sha256WorkingLocs]) (h1 := by simp [sha256WorkingLocs])
      (h2 := by simp [sha256WorkingLocs]) (h3 := by simp [sha256WorkingLocs])]; miden_bind
  rw [stepPadw]; miden_bind
  rw [stepLocLoadwBe 0 a b c d
      (h0 := by simp [sha256WorkingLocs]) (h1 := by simp [sha256WorkingLocs])
      (h2 := by simp [sha256WorkingLocs]) (h3 := by simp [sha256WorkingLocs])]; miden_bind
  simp only [show sha256ProcEnv "consume_message_word" =
      some Miden.Core.Sha256.consume_message_word from rfl]
  rw [consume_message_word_at_2125 a b c d e f g h (Felt.ofNat 430227734) W48
      _ _ rfl ha hb hc hd he hf hg hh (felt_ofNat_isU32_of_lt _ (by norm_num)) hW48]
  simp only [MidenState.withStack]
  rw [stepPush]; miden_bind
  rw [stepMovdn (hn := rfl)]; miden_bind
  rw [consume_message_word_at_2125 _ _ _ _ _ _ _ _ (Felt.ofNat 506948616) W49
      _ _ rfl (u32_mod_isU32 _) ha hb hc (u32_mod_isU32 _) he hf hg
      (felt_ofNat_isU32_of_lt _ (by norm_num)) hW49]
  simp only [MidenState.withStack]
  rw [stepPush]; miden_bind
  rw [stepMovdn (hn := rfl)]; miden_bind
  rw [consume_message_word_at_2125 _ _ _ _ _ _ _ _ (Felt.ofNat 659060556) W50
      _ _ rfl (u32_mod_isU32 _) (u32_mod_isU32 _) ha hb (u32_mod_isU32 _) (u32_mod_isU32 _)
      he hf (felt_ofNat_isU32_of_lt _ (by norm_num)) hW50]
  simp only [MidenState.withStack]
  rw [stepPush]; miden_bind
  rw [stepMovdn (hn := rfl)]; miden_bind
  rw [consume_message_word_at_2125 _ _ _ _ _ _ _ _ (Felt.ofNat 883997877) W51
      _ _ rfl (u32_mod_isU32 _) (u32_mod_isU32 _) (u32_mod_isU32 _) ha (u32_mod_isU32 _)
      (u32_mod_isU32 _) (u32_mod_isU32 _) he (felt_ofNat_isU32_of_lt _ (by norm_num)) hW51]
  simp only [MidenState.withStack]
  dsimp only [pure, Pure.pure, bind, Bind.bind, Option.bind]
  -- Part C: trailing rearrange [movupw 2, rev_element_order, movdnw 2]
  simp only [sha256SB12TrailingOps]
  unfold execWithEnv; simp only [List.foldlM]
  rw [stepMovupw2]; miden_bind
  simp only [show sha256ProcEnv "rev_element_order" =
      some Miden.Core.Sha256.rev_element_order from rfl]
  rw [rev_element_order_at_2125]; simp only [bind, Bind.bind, Option.bind]
  rw [stepMovdnw2]; miden_bind
  dsimp only [pure, Pure.pure]
  simp only [sha256Compress4, consumeResult]

-- ============================================================================
-- SB13 bridge
-- Input:  [a,..,h, W52,W53,W54,W55, W59,W58,W57,W56, W63,W62,W61,W60, rest]
-- Output: [na,..,nh, W56,W57,W58,W59, W63,W62,W61,W60, rest]
-- Locs: not accessed
-- ============================================================================

set_option maxHeartbeats 4000000 in
lemma sha256_SB13_bridge
    (a b c d e f g h : Felt)
    (W52 W53 W54 W55 W59 W58 W57 W56 W63 W62 W61 W60 : Felt)
    (hW52 : W52.isU32 = true) (hW53 : W53.isU32 = true)
    (hW54 : W54.isU32 = true) (hW55 : W55.isU32 = true)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hc : c.isU32 = true) (hd : d.isU32 = true)
    (he : e.isU32 = true) (hf : f.isU32 = true) (hg : g.isU32 = true) (hh : h.isU32 = true)
    (rest : List Felt) (mem locs : Nat → Felt) (adv : List Felt) :
    let (na, nb, nc, nd, ne, nf, ng, nh) :=
      sha256Compress4 a b c d e f g h W52 W53 W54 W55 958139571 1322822218 1537002063 1747873779
    execWithEnv sha256ProcEnv 2126
        ⟨a::b::c::d::e::f::g::h::W52::W53::W54::W55::W59::W58::W57::W56::W63::W62::W61::W60::rest,
          mem, locs, adv⟩
        sha256SB13Ops =
    some ⟨na :: nb :: nc :: nd :: ne :: nf :: ng :: nh ::
          W56 :: W57 :: W58 :: W59 :: W63 :: W62 :: W61 :: W60 :: rest,
          mem, locs, adv⟩ := by
  rw [sha256SB13Ops_split, execWithEnv_append]
  -- Consume 4 rounds
  rw [show sha256SB13ConsumeOps = [.inst (.push 958139571), .inst (.movdn 8),
       .inst (.exec "consume_message_word"),
       .inst (.push 1322822218), .inst (.movdn 8),
       .inst (.exec "consume_message_word"),
       .inst (.push 1537002063), .inst (.movdn 8),
       .inst (.exec "consume_message_word"),
       .inst (.push 1747873779), .inst (.movdn 8),
       .inst (.exec "consume_message_word")] from rfl]
  rw [sha256_stack_consume4_bridge a b c d e f g h W52 W53 W54 W55
      (W59::W58::W57::W56::W63::W62::W61::W60::rest)
      958139571 1322822218 1537002063 1747873779
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hW52 hW53 hW54 hW55 ha hb hc hd he hf hg hh mem locs adv]
  simp only [bind, Bind.bind, Option.bind]
  -- Trailing rearrange
  rw [show sha256SB13TrailingOps = [.inst (.movupw 2), .inst (.exec "rev_element_order"),
       .inst (.movdnw 2)] from rfl]
  rw [sha256_trailing_rearrange_bridge _ _ _ _ _ _ _ _ W59 W58 W57 W56
      (W63::W62::W61::W60::rest) mem locs adv]
  simp only [sha256Compress4, consumeResult]

-- ============================================================================
-- SB14 bridge
-- Input:  [a,..,h, W56,W57,W58,W59, W63,W62,W61,W60, rest]
-- Output: [na,..,nh, W60,W61,W62,W63, rest]
-- Locs: not accessed
-- ============================================================================

set_option maxHeartbeats 4000000 in
lemma sha256_SB14_bridge
    (a b c d e f g h : Felt)
    (W56 W57 W58 W59 W63 W62 W61 W60 : Felt)
    (hW56 : W56.isU32 = true) (hW57 : W57.isU32 = true)
    (hW58 : W58.isU32 = true) (hW59 : W59.isU32 = true)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hc : c.isU32 = true) (hd : d.isU32 = true)
    (he : e.isU32 = true) (hf : f.isU32 = true) (hg : g.isU32 = true) (hh : h.isU32 = true)
    (rest : List Felt) (mem locs : Nat → Felt) (adv : List Felt) :
    let (na, nb, nc, nd, ne, nf, ng, nh) :=
      sha256Compress4 a b c d e f g h W56 W57 W58 W59 1955562222 2024104815 2227730452 2361852424
    execWithEnv sha256ProcEnv 2126
        ⟨a::b::c::d::e::f::g::h::W56::W57::W58::W59::W63::W62::W61::W60::rest,
          mem, locs, adv⟩
        sha256SB14Ops =
    some ⟨na :: nb :: nc :: nd :: ne :: nf :: ng :: nh ::
          W60 :: W61 :: W62 :: W63 :: rest,
          mem, locs, adv⟩ := by
  rw [sha256SB14Ops_split, execWithEnv_append]
  -- Consume 4 rounds
  rw [show sha256SB14ConsumeOps = [.inst (.push 1955562222), .inst (.movdn 8),
       .inst (.exec "consume_message_word"),
       .inst (.push 2024104815), .inst (.movdn 8),
       .inst (.exec "consume_message_word"),
       .inst (.push 2227730452), .inst (.movdn 8),
       .inst (.exec "consume_message_word"),
       .inst (.push 2361852424), .inst (.movdn 8),
       .inst (.exec "consume_message_word")] from rfl]
  rw [sha256_stack_consume4_bridge a b c d e f g h W56 W57 W58 W59
      (W63::W62::W61::W60::rest)
      1955562222 2024104815 2227730452 2361852424
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hW56 hW57 hW58 hW59 ha hb hc hd he hf hg hh mem locs adv]
  simp only [bind, Bind.bind, Option.bind]
  -- Trailing rearrange
  rw [show sha256SB14TrailingOps = [.inst (.movupw 2), .inst (.exec "rev_element_order"),
       .inst (.movdnw 2)] from rfl]
  rw [sha256_trailing_rearrange_bridge _ _ _ _ _ _ _ _ W63 W62 W61 W60
      rest mem locs adv]
  simp only [sha256Compress4, consumeResult]

-- ============================================================================
-- SB15 bridge
-- Input:  [a,..,h, W60,W61,W62,W63, rest]
-- Output: [na,..,nh, rest]
-- Locs: not accessed
-- ============================================================================

set_option maxHeartbeats 4000000 in
lemma sha256_SB15_bridge
    (a b c d e f g h : Felt)
    (W60 W61 W62 W63 : Felt)
    (hW60 : W60.isU32 = true) (hW61 : W61.isU32 = true)
    (hW62 : W62.isU32 = true) (hW63 : W63.isU32 = true)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hc : c.isU32 = true) (hd : d.isU32 = true)
    (he : e.isU32 = true) (hf : f.isU32 = true) (hg : g.isU32 = true) (hh : h.isU32 = true)
    (rest : List Felt) (mem locs : Nat → Felt) (adv : List Felt) :
    let (na, nb, nc, nd, ne, nf, ng, nh) :=
      sha256Compress4 a b c d e f g h W60 W61 W62 W63 2428436474 2756734187 3204031479 3329325298
    execWithEnv sha256ProcEnv 2126
        ⟨a::b::c::d::e::f::g::h::W60::W61::W62::W63::rest,
          mem, locs, adv⟩
        sha256SB15Ops =
    some ⟨na :: nb :: nc :: nd :: ne :: nf :: ng :: nh :: rest,
          mem, locs, adv⟩ := by
  rw [sha256SB15Ops_eq]
  rw [sha256_stack_consume4_bridge a b c d e f g h W60 W61 W62 W63 rest
      2428436474 2756734187 3204031479 3329325298
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hW60 hW61 hW62 hW63 ha hb hc hd he hf hg hh mem locs adv]
  simp only [sha256Compress4, consumeResult]


end MidenLean.Proofs.Sha256
