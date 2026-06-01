import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block233

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block233

open Set

def block233W1 : Rat := ((8644615711612729 : Rat) / 10000000000000000)
def block233W2 : Rat := ((4187347126343171 : Rat) / 50000000000000000)
def block233W3 : Rat := ((9101072221642867 : Rat) / 50000000000000000)
def block233W4 : Rat := ((3534148804307491 : Rat) / 50000000000000000)
def block233S1 : Rat := ((18174751 : Rat) / 10000000)
def block233S2 : Rat := ((511587 : Rat) / 200000)
def block233S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block233S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block233V (y : ℝ) : ℝ :=
  ratPotential block233W1 block233W2 block233W3 block233W4 block233S1 block233S2 block233S3 block233S4 y

def block233LeftParamsCertificate : Bool :=
  allBoxesSameParams block233LeftBoxes block233W1 block233W2 block233W3 block233W4 block233S1 block233S2 block233S3 block233S4

theorem block233LeftParamsCertificate_eq_true :
    block233LeftParamsCertificate = true := by
  native_decide

theorem block233_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block233LeftL : ℝ) (block233LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block233S1 : ℝ))
    (hy2ne : y ≠ (block233S2 : ℝ))
    (hy3ne : y ≠ (block233S3 : ℝ))
    (hy4ne : y ≠ (block233S4 : ℝ)) :
    0 < block233V y := by
  have hcert := block233LeftCertificate_eq_true
  unfold block233LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block233LeftBoxes) (lo := block233LeftL) (hi := block233LeftR)
    (w1 := block233W1) (w2 := block233W2) (w3 := block233W3) (w4 := block233W4)
    (s1 := block233S1) (s2 := block233S2) (s3 := block233S3) (s4 := block233S4)
    hboxes hcover block233LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block233RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block233RightChunk000 block233W1 block233W2 block233W3 block233W4 block233S1 block233S2 block233S3 block233S4

theorem block233RightChunk000ParamsCertificate_eq_true :
    block233RightChunk000ParamsCertificate = true := by
  native_decide

theorem block233_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block233RightChunk000L : ℝ) (block233RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block233S1 : ℝ))
    (hy2ne : y ≠ (block233S2 : ℝ))
    (hy3ne : y ≠ (block233S3 : ℝ))
    (hy4ne : y ≠ (block233S4 : ℝ)) :
    0 < block233V y := by
  have hcert := block233RightChunk000Certificate_eq_true
  unfold block233RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block233RightChunk000) (lo := block233RightChunk000L) (hi := block233RightChunk000R)
    (w1 := block233W1) (w2 := block233W2) (w3 := block233W3) (w4 := block233W4)
    (s1 := block233S1) (s2 := block233S2) (s3 := block233S3) (s4 := block233S4)
    hboxes hcover block233RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block233RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block233RightChunk001 block233W1 block233W2 block233W3 block233W4 block233S1 block233S2 block233S3 block233S4

theorem block233RightChunk001ParamsCertificate_eq_true :
    block233RightChunk001ParamsCertificate = true := by
  native_decide

theorem block233_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block233RightChunk001L : ℝ) (block233RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block233S1 : ℝ))
    (hy2ne : y ≠ (block233S2 : ℝ))
    (hy3ne : y ≠ (block233S3 : ℝ))
    (hy4ne : y ≠ (block233S4 : ℝ)) :
    0 < block233V y := by
  have hcert := block233RightChunk001Certificate_eq_true
  unfold block233RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block233RightChunk001) (lo := block233RightChunk001L) (hi := block233RightChunk001R)
    (w1 := block233W1) (w2 := block233W2) (w3 := block233W3) (w4 := block233W4)
    (s1 := block233S1) (s2 := block233S2) (s3 := block233S3) (s4 := block233S4)
    hboxes hcover block233RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block233RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block233RightChunk002 block233W1 block233W2 block233W3 block233W4 block233S1 block233S2 block233S3 block233S4

theorem block233RightChunk002ParamsCertificate_eq_true :
    block233RightChunk002ParamsCertificate = true := by
  native_decide

theorem block233_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block233RightChunk002L : ℝ) (block233RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block233S1 : ℝ))
    (hy2ne : y ≠ (block233S2 : ℝ))
    (hy3ne : y ≠ (block233S3 : ℝ))
    (hy4ne : y ≠ (block233S4 : ℝ)) :
    0 < block233V y := by
  have hcert := block233RightChunk002Certificate_eq_true
  unfold block233RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block233RightChunk002) (lo := block233RightChunk002L) (hi := block233RightChunk002R)
    (w1 := block233W1) (w2 := block233W2) (w3 := block233W3) (w4 := block233W4)
    (s1 := block233S1) (s2 := block233S2) (s3 := block233S3) (s4 := block233S4)
    hboxes hcover block233RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block233_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block233RightL : ℝ) (block233RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block233S1 : ℝ))
    (hy2ne : y ≠ (block233S2 : ℝ))
    (hy3ne : y ≠ (block233S3 : ℝ))
    (hy4ne : y ≠ (block233S4 : ℝ)) :
    0 < block233V y := by
  by_cases h0 : y ≤ (block233RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block233RightChunk000L : ℝ) (block233RightChunk000R : ℝ) := by
      have hL : (block233RightChunk000L : ℝ) = (block233RightL : ℝ) := by
        norm_num [block233RightChunk000L, block233RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block233_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block233RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block233RightChunk001L : ℝ) (block233RightChunk001R : ℝ) := by
        have hprev : (block233RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block233RightChunk001L : ℝ) = (block233RightChunk000R : ℝ) := by
          norm_num [block233RightChunk001L, block233RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block233_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      have hprev : (block233RightChunk001R : ℝ) < y := lt_of_not_ge h1
      have hL : (block233RightChunk002L : ℝ) = (block233RightChunk001R : ℝ) := by
        norm_num [block233RightChunk002L, block233RightChunk001R]
      have hR : (block233RightChunk002R : ℝ) = (block233RightR : ℝ) := by
        norm_num [block233RightChunk002R, block233RightR]
      have hyc : y ∈ Icc (block233RightChunk002L : ℝ) (block233RightChunk002R : ℝ) := by
        constructor
        · linarith [hprev, hL]
        · linarith [hy.2, hR]
      exact block233_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block233_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block233LeftL : ℝ) (block233LeftR : ℝ) →
    y ≠ 0 → y ≠ (block233S1 : ℝ) → y ≠ (block233S2 : ℝ) →
    y ≠ (block233S3 : ℝ) → y ≠ (block233S4 : ℝ) → 0 < block233V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block233RightL : ℝ) (block233RightR : ℝ) →
    y ≠ 0 → y ≠ (block233S1 : ℝ) → y ≠ (block233S2 : ℝ) →
    y ≠ (block233S3 : ℝ) → y ≠ (block233S4 : ℝ) → 0 < block233V y)

theorem block233_reallog_certificate_proof :
    block233_reallog_certificate := by
  exact ⟨block233_left_V_pos, block233_right_V_pos⟩

end Block233
end M1817475
end Erdos1038Lean
