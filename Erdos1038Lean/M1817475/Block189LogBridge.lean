import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block189

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block189

open Set

def block189W1 : Rat := ((1755381605390141 : Rat) / 1000000000000000)
def block189W2 : Rat := (0 : Rat)
def block189W3 : Rat := ((8945740556431009 : Rat) / 50000000000000000)
def block189W4 : Rat := ((9326946830381519 : Rat) / 100000000000000000)
def block189S1 : Rat := ((18174751 : Rat) / 10000000)
def block189S2 : Rat := ((511587 : Rat) / 200000)
def block189S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block189S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block189V (y : ℝ) : ℝ :=
  ratPotential block189W1 block189W2 block189W3 block189W4 block189S1 block189S2 block189S3 block189S4 y

def block189LeftParamsCertificate : Bool :=
  allBoxesSameParams block189LeftBoxes block189W1 block189W2 block189W3 block189W4 block189S1 block189S2 block189S3 block189S4

theorem block189LeftParamsCertificate_eq_true :
    block189LeftParamsCertificate = true := by
  native_decide

theorem block189_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block189LeftL : ℝ) (block189LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block189S1 : ℝ))
    (hy2ne : y ≠ (block189S2 : ℝ))
    (hy3ne : y ≠ (block189S3 : ℝ))
    (hy4ne : y ≠ (block189S4 : ℝ)) :
    0 < block189V y := by
  have hcert := block189LeftCertificate_eq_true
  unfold block189LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block189LeftBoxes) (lo := block189LeftL) (hi := block189LeftR)
    (w1 := block189W1) (w2 := block189W2) (w3 := block189W3) (w4 := block189W4)
    (s1 := block189S1) (s2 := block189S2) (s3 := block189S3) (s4 := block189S4)
    hboxes hcover block189LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block189RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block189RightChunk000 block189W1 block189W2 block189W3 block189W4 block189S1 block189S2 block189S3 block189S4

theorem block189RightChunk000ParamsCertificate_eq_true :
    block189RightChunk000ParamsCertificate = true := by
  native_decide

theorem block189_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block189RightChunk000L : ℝ) (block189RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block189S1 : ℝ))
    (hy2ne : y ≠ (block189S2 : ℝ))
    (hy3ne : y ≠ (block189S3 : ℝ))
    (hy4ne : y ≠ (block189S4 : ℝ)) :
    0 < block189V y := by
  have hcert := block189RightChunk000Certificate_eq_true
  unfold block189RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block189RightChunk000) (lo := block189RightChunk000L) (hi := block189RightChunk000R)
    (w1 := block189W1) (w2 := block189W2) (w3 := block189W3) (w4 := block189W4)
    (s1 := block189S1) (s2 := block189S2) (s3 := block189S3) (s4 := block189S4)
    hboxes hcover block189RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block189RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block189RightChunk001 block189W1 block189W2 block189W3 block189W4 block189S1 block189S2 block189S3 block189S4

theorem block189RightChunk001ParamsCertificate_eq_true :
    block189RightChunk001ParamsCertificate = true := by
  native_decide

theorem block189_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block189RightChunk001L : ℝ) (block189RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block189S1 : ℝ))
    (hy2ne : y ≠ (block189S2 : ℝ))
    (hy3ne : y ≠ (block189S3 : ℝ))
    (hy4ne : y ≠ (block189S4 : ℝ)) :
    0 < block189V y := by
  have hcert := block189RightChunk001Certificate_eq_true
  unfold block189RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block189RightChunk001) (lo := block189RightChunk001L) (hi := block189RightChunk001R)
    (w1 := block189W1) (w2 := block189W2) (w3 := block189W3) (w4 := block189W4)
    (s1 := block189S1) (s2 := block189S2) (s3 := block189S3) (s4 := block189S4)
    hboxes hcover block189RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block189RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block189RightChunk002 block189W1 block189W2 block189W3 block189W4 block189S1 block189S2 block189S3 block189S4

theorem block189RightChunk002ParamsCertificate_eq_true :
    block189RightChunk002ParamsCertificate = true := by
  native_decide

theorem block189_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block189RightChunk002L : ℝ) (block189RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block189S1 : ℝ))
    (hy2ne : y ≠ (block189S2 : ℝ))
    (hy3ne : y ≠ (block189S3 : ℝ))
    (hy4ne : y ≠ (block189S4 : ℝ)) :
    0 < block189V y := by
  have hcert := block189RightChunk002Certificate_eq_true
  unfold block189RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block189RightChunk002) (lo := block189RightChunk002L) (hi := block189RightChunk002R)
    (w1 := block189W1) (w2 := block189W2) (w3 := block189W3) (w4 := block189W4)
    (s1 := block189S1) (s2 := block189S2) (s3 := block189S3) (s4 := block189S4)
    hboxes hcover block189RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block189_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block189RightL : ℝ) (block189RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block189S1 : ℝ))
    (hy2ne : y ≠ (block189S2 : ℝ))
    (hy3ne : y ≠ (block189S3 : ℝ))
    (hy4ne : y ≠ (block189S4 : ℝ)) :
    0 < block189V y := by
  by_cases h0 : y ≤ (block189RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block189RightChunk000L : ℝ) (block189RightChunk000R : ℝ) := by
      have hL : (block189RightChunk000L : ℝ) = (block189RightL : ℝ) := by
        norm_num [block189RightChunk000L, block189RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block189_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block189RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block189RightChunk001L : ℝ) (block189RightChunk001R : ℝ) := by
        have hprev : (block189RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block189RightChunk001L : ℝ) = (block189RightChunk000R : ℝ) := by
          norm_num [block189RightChunk001L, block189RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block189_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      have hprev : (block189RightChunk001R : ℝ) < y := lt_of_not_ge h1
      have hL : (block189RightChunk002L : ℝ) = (block189RightChunk001R : ℝ) := by
        norm_num [block189RightChunk002L, block189RightChunk001R]
      have hR : (block189RightChunk002R : ℝ) = (block189RightR : ℝ) := by
        norm_num [block189RightChunk002R, block189RightR]
      have hyc : y ∈ Icc (block189RightChunk002L : ℝ) (block189RightChunk002R : ℝ) := by
        constructor
        · linarith [hprev, hL]
        · linarith [hy.2, hR]
      exact block189_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block189_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block189LeftL : ℝ) (block189LeftR : ℝ) →
    y ≠ 0 → y ≠ (block189S1 : ℝ) → y ≠ (block189S2 : ℝ) →
    y ≠ (block189S3 : ℝ) → y ≠ (block189S4 : ℝ) → 0 < block189V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block189RightL : ℝ) (block189RightR : ℝ) →
    y ≠ 0 → y ≠ (block189S1 : ℝ) → y ≠ (block189S2 : ℝ) →
    y ≠ (block189S3 : ℝ) → y ≠ (block189S4 : ℝ) → 0 < block189V y)

theorem block189_reallog_certificate_proof :
    block189_reallog_certificate := by
  exact ⟨block189_left_V_pos, block189_right_V_pos⟩

end Block189
end M1817475
end Erdos1038Lean
