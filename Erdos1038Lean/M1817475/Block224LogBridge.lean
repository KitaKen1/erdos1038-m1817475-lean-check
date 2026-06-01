import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block224

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block224

open Set

def block224W1 : Rat := ((1196759653186871 : Rat) / 1250000000000000)
def block224W2 : Rat := ((2792930042478167 : Rat) / 50000000000000000)
def block224W3 : Rat := ((4290507247270179 : Rat) / 25000000000000000)
def block224W4 : Rat := ((2478552101499503 : Rat) / 25000000000000000)
def block224S1 : Rat := ((18174751 : Rat) / 10000000)
def block224S2 : Rat := ((511587 : Rat) / 200000)
def block224S3 : Rat := ((135344025982142857073 : Rat) / 50000000000000000000)
def block224S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block224V (y : ℝ) : ℝ :=
  ratPotential block224W1 block224W2 block224W3 block224W4 block224S1 block224S2 block224S3 block224S4 y

def block224LeftParamsCertificate : Bool :=
  allBoxesSameParams block224LeftBoxes block224W1 block224W2 block224W3 block224W4 block224S1 block224S2 block224S3 block224S4

theorem block224LeftParamsCertificate_eq_true :
    block224LeftParamsCertificate = true := by
  native_decide

theorem block224_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block224LeftL : ℝ) (block224LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block224S1 : ℝ))
    (hy2ne : y ≠ (block224S2 : ℝ))
    (hy3ne : y ≠ (block224S3 : ℝ))
    (hy4ne : y ≠ (block224S4 : ℝ)) :
    0 < block224V y := by
  have hcert := block224LeftCertificate_eq_true
  unfold block224LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block224LeftBoxes) (lo := block224LeftL) (hi := block224LeftR)
    (w1 := block224W1) (w2 := block224W2) (w3 := block224W3) (w4 := block224W4)
    (s1 := block224S1) (s2 := block224S2) (s3 := block224S3) (s4 := block224S4)
    hboxes hcover block224LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block224RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block224RightChunk000 block224W1 block224W2 block224W3 block224W4 block224S1 block224S2 block224S3 block224S4

theorem block224RightChunk000ParamsCertificate_eq_true :
    block224RightChunk000ParamsCertificate = true := by
  native_decide

theorem block224_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block224RightChunk000L : ℝ) (block224RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block224S1 : ℝ))
    (hy2ne : y ≠ (block224S2 : ℝ))
    (hy3ne : y ≠ (block224S3 : ℝ))
    (hy4ne : y ≠ (block224S4 : ℝ)) :
    0 < block224V y := by
  have hcert := block224RightChunk000Certificate_eq_true
  unfold block224RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block224RightChunk000) (lo := block224RightChunk000L) (hi := block224RightChunk000R)
    (w1 := block224W1) (w2 := block224W2) (w3 := block224W3) (w4 := block224W4)
    (s1 := block224S1) (s2 := block224S2) (s3 := block224S3) (s4 := block224S4)
    hboxes hcover block224RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block224RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block224RightChunk001 block224W1 block224W2 block224W3 block224W4 block224S1 block224S2 block224S3 block224S4

theorem block224RightChunk001ParamsCertificate_eq_true :
    block224RightChunk001ParamsCertificate = true := by
  native_decide

theorem block224_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block224RightChunk001L : ℝ) (block224RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block224S1 : ℝ))
    (hy2ne : y ≠ (block224S2 : ℝ))
    (hy3ne : y ≠ (block224S3 : ℝ))
    (hy4ne : y ≠ (block224S4 : ℝ)) :
    0 < block224V y := by
  have hcert := block224RightChunk001Certificate_eq_true
  unfold block224RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block224RightChunk001) (lo := block224RightChunk001L) (hi := block224RightChunk001R)
    (w1 := block224W1) (w2 := block224W2) (w3 := block224W3) (w4 := block224W4)
    (s1 := block224S1) (s2 := block224S2) (s3 := block224S3) (s4 := block224S4)
    hboxes hcover block224RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block224RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block224RightChunk002 block224W1 block224W2 block224W3 block224W4 block224S1 block224S2 block224S3 block224S4

theorem block224RightChunk002ParamsCertificate_eq_true :
    block224RightChunk002ParamsCertificate = true := by
  native_decide

theorem block224_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block224RightChunk002L : ℝ) (block224RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block224S1 : ℝ))
    (hy2ne : y ≠ (block224S2 : ℝ))
    (hy3ne : y ≠ (block224S3 : ℝ))
    (hy4ne : y ≠ (block224S4 : ℝ)) :
    0 < block224V y := by
  have hcert := block224RightChunk002Certificate_eq_true
  unfold block224RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block224RightChunk002) (lo := block224RightChunk002L) (hi := block224RightChunk002R)
    (w1 := block224W1) (w2 := block224W2) (w3 := block224W3) (w4 := block224W4)
    (s1 := block224S1) (s2 := block224S2) (s3 := block224S3) (s4 := block224S4)
    hboxes hcover block224RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block224_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block224RightL : ℝ) (block224RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block224S1 : ℝ))
    (hy2ne : y ≠ (block224S2 : ℝ))
    (hy3ne : y ≠ (block224S3 : ℝ))
    (hy4ne : y ≠ (block224S4 : ℝ)) :
    0 < block224V y := by
  by_cases h0 : y ≤ (block224RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block224RightChunk000L : ℝ) (block224RightChunk000R : ℝ) := by
      have hL : (block224RightChunk000L : ℝ) = (block224RightL : ℝ) := by
        norm_num [block224RightChunk000L, block224RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block224_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block224RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block224RightChunk001L : ℝ) (block224RightChunk001R : ℝ) := by
        have hprev : (block224RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block224RightChunk001L : ℝ) = (block224RightChunk000R : ℝ) := by
          norm_num [block224RightChunk001L, block224RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block224_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      have hprev : (block224RightChunk001R : ℝ) < y := lt_of_not_ge h1
      have hL : (block224RightChunk002L : ℝ) = (block224RightChunk001R : ℝ) := by
        norm_num [block224RightChunk002L, block224RightChunk001R]
      have hR : (block224RightChunk002R : ℝ) = (block224RightR : ℝ) := by
        norm_num [block224RightChunk002R, block224RightR]
      have hyc : y ∈ Icc (block224RightChunk002L : ℝ) (block224RightChunk002R : ℝ) := by
        constructor
        · linarith [hprev, hL]
        · linarith [hy.2, hR]
      exact block224_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block224_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block224LeftL : ℝ) (block224LeftR : ℝ) →
    y ≠ 0 → y ≠ (block224S1 : ℝ) → y ≠ (block224S2 : ℝ) →
    y ≠ (block224S3 : ℝ) → y ≠ (block224S4 : ℝ) → 0 < block224V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block224RightL : ℝ) (block224RightR : ℝ) →
    y ≠ 0 → y ≠ (block224S1 : ℝ) → y ≠ (block224S2 : ℝ) →
    y ≠ (block224S3 : ℝ) → y ≠ (block224S4 : ℝ) → 0 < block224V y)

theorem block224_reallog_certificate_proof :
    block224_reallog_certificate := by
  exact ⟨block224_left_V_pos, block224_right_V_pos⟩

end Block224
end M1817475
end Erdos1038Lean
