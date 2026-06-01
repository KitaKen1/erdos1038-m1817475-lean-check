import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block242

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block242

open Set

def block242W1 : Rat := ((1718821204698449 : Rat) / 2000000000000000)
def block242W2 : Rat := ((8451329487441343 : Rat) / 100000000000000000)
def block242W3 : Rat := ((9369465095678469 : Rat) / 250000000000000000)
def block242W4 : Rat := ((2147771718128377 : Rat) / 10000000000000000)
def block242S1 : Rat := ((18174751 : Rat) / 10000000)
def block242S2 : Rat := ((511587 : Rat) / 200000)
def block242S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block242S4 : Rat := ((3421965897321428449 : Rat) / 1250000000000000000)

noncomputable def block242V (y : ℝ) : ℝ :=
  ratPotential block242W1 block242W2 block242W3 block242W4 block242S1 block242S2 block242S3 block242S4 y

def block242LeftParamsCertificate : Bool :=
  allBoxesSameParams block242LeftBoxes block242W1 block242W2 block242W3 block242W4 block242S1 block242S2 block242S3 block242S4

theorem block242LeftParamsCertificate_eq_true :
    block242LeftParamsCertificate = true := by
  native_decide

theorem block242_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block242LeftL : ℝ) (block242LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block242S1 : ℝ))
    (hy2ne : y ≠ (block242S2 : ℝ))
    (hy3ne : y ≠ (block242S3 : ℝ))
    (hy4ne : y ≠ (block242S4 : ℝ)) :
    0 < block242V y := by
  have hcert := block242LeftCertificate_eq_true
  unfold block242LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block242LeftBoxes) (lo := block242LeftL) (hi := block242LeftR)
    (w1 := block242W1) (w2 := block242W2) (w3 := block242W3) (w4 := block242W4)
    (s1 := block242S1) (s2 := block242S2) (s3 := block242S3) (s4 := block242S4)
    hboxes hcover block242LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block242RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block242RightChunk000 block242W1 block242W2 block242W3 block242W4 block242S1 block242S2 block242S3 block242S4

theorem block242RightChunk000ParamsCertificate_eq_true :
    block242RightChunk000ParamsCertificate = true := by
  native_decide

theorem block242_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block242RightChunk000L : ℝ) (block242RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block242S1 : ℝ))
    (hy2ne : y ≠ (block242S2 : ℝ))
    (hy3ne : y ≠ (block242S3 : ℝ))
    (hy4ne : y ≠ (block242S4 : ℝ)) :
    0 < block242V y := by
  have hcert := block242RightChunk000Certificate_eq_true
  unfold block242RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block242RightChunk000) (lo := block242RightChunk000L) (hi := block242RightChunk000R)
    (w1 := block242W1) (w2 := block242W2) (w3 := block242W3) (w4 := block242W4)
    (s1 := block242S1) (s2 := block242S2) (s3 := block242S3) (s4 := block242S4)
    hboxes hcover block242RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block242RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block242RightChunk001 block242W1 block242W2 block242W3 block242W4 block242S1 block242S2 block242S3 block242S4

theorem block242RightChunk001ParamsCertificate_eq_true :
    block242RightChunk001ParamsCertificate = true := by
  native_decide

theorem block242_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block242RightChunk001L : ℝ) (block242RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block242S1 : ℝ))
    (hy2ne : y ≠ (block242S2 : ℝ))
    (hy3ne : y ≠ (block242S3 : ℝ))
    (hy4ne : y ≠ (block242S4 : ℝ)) :
    0 < block242V y := by
  have hcert := block242RightChunk001Certificate_eq_true
  unfold block242RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block242RightChunk001) (lo := block242RightChunk001L) (hi := block242RightChunk001R)
    (w1 := block242W1) (w2 := block242W2) (w3 := block242W3) (w4 := block242W4)
    (s1 := block242S1) (s2 := block242S2) (s3 := block242S3) (s4 := block242S4)
    hboxes hcover block242RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block242_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block242RightL : ℝ) (block242RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block242S1 : ℝ))
    (hy2ne : y ≠ (block242S2 : ℝ))
    (hy3ne : y ≠ (block242S3 : ℝ))
    (hy4ne : y ≠ (block242S4 : ℝ)) :
    0 < block242V y := by
  by_cases h0 : y ≤ (block242RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block242RightChunk000L : ℝ) (block242RightChunk000R : ℝ) := by
      have hL : (block242RightChunk000L : ℝ) = (block242RightL : ℝ) := by
        norm_num [block242RightChunk000L, block242RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block242_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block242RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block242RightChunk001L : ℝ) = (block242RightChunk000R : ℝ) := by
      norm_num [block242RightChunk001L, block242RightChunk000R]
    have hR : (block242RightChunk001R : ℝ) = (block242RightR : ℝ) := by
      norm_num [block242RightChunk001R, block242RightR]
    have hyc : y ∈ Icc (block242RightChunk001L : ℝ) (block242RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block242_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block242_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block242LeftL : ℝ) (block242LeftR : ℝ) →
    y ≠ 0 → y ≠ (block242S1 : ℝ) → y ≠ (block242S2 : ℝ) →
    y ≠ (block242S3 : ℝ) → y ≠ (block242S4 : ℝ) → 0 < block242V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block242RightL : ℝ) (block242RightR : ℝ) →
    y ≠ 0 → y ≠ (block242S1 : ℝ) → y ≠ (block242S2 : ℝ) →
    y ≠ (block242S3 : ℝ) → y ≠ (block242S4 : ℝ) → 0 < block242V y)

theorem block242_reallog_certificate_proof :
    block242_reallog_certificate := by
  exact ⟨block242_left_V_pos, block242_right_V_pos⟩

end Block242
end M1817475
end Erdos1038Lean
