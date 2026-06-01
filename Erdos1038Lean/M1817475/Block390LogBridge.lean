import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block390

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block390

open Set

def block390W1 : Rat := ((8068130959934263 : Rat) / 10000000000000000)
def block390W2 : Rat := ((10298553719643791 : Rat) / 250000000000000000)
def block390W3 : Rat := ((2139055443501027 : Rat) / 12500000000000000)
def block390W4 : Rat := ((728430234131617 : Rat) / 5000000000000000)
def block390S1 : Rat := ((18174751 : Rat) / 10000000)
def block390S2 : Rat := ((511587 : Rat) / 200000)
def block390S3 : Rat := ((132509405446428571483 : Rat) / 50000000000000000000)
def block390S4 : Rat := ((34776808526785713037 : Rat) / 12500000000000000000)

noncomputable def block390V (y : ℝ) : ℝ :=
  ratPotential block390W1 block390W2 block390W3 block390W4 block390S1 block390S2 block390S3 block390S4 y

def block390LeftParamsCertificate : Bool :=
  allBoxesSameParams block390LeftBoxes block390W1 block390W2 block390W3 block390W4 block390S1 block390S2 block390S3 block390S4

theorem block390LeftParamsCertificate_eq_true :
    block390LeftParamsCertificate = true := by
  native_decide

theorem block390_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block390LeftL : ℝ) (block390LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block390S1 : ℝ))
    (hy2ne : y ≠ (block390S2 : ℝ))
    (hy3ne : y ≠ (block390S3 : ℝ))
    (hy4ne : y ≠ (block390S4 : ℝ)) :
    0 < block390V y := by
  have hcert := block390LeftCertificate_eq_true
  unfold block390LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block390LeftBoxes) (lo := block390LeftL) (hi := block390LeftR)
    (w1 := block390W1) (w2 := block390W2) (w3 := block390W3) (w4 := block390W4)
    (s1 := block390S1) (s2 := block390S2) (s3 := block390S3) (s4 := block390S4)
    hboxes hcover block390LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block390RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block390RightChunk000 block390W1 block390W2 block390W3 block390W4 block390S1 block390S2 block390S3 block390S4

theorem block390RightChunk000ParamsCertificate_eq_true :
    block390RightChunk000ParamsCertificate = true := by
  native_decide

theorem block390_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block390RightChunk000L : ℝ) (block390RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block390S1 : ℝ))
    (hy2ne : y ≠ (block390S2 : ℝ))
    (hy3ne : y ≠ (block390S3 : ℝ))
    (hy4ne : y ≠ (block390S4 : ℝ)) :
    0 < block390V y := by
  have hcert := block390RightChunk000Certificate_eq_true
  unfold block390RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block390RightChunk000) (lo := block390RightChunk000L) (hi := block390RightChunk000R)
    (w1 := block390W1) (w2 := block390W2) (w3 := block390W3) (w4 := block390W4)
    (s1 := block390S1) (s2 := block390S2) (s3 := block390S3) (s4 := block390S4)
    hboxes hcover block390RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block390RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block390RightChunk001 block390W1 block390W2 block390W3 block390W4 block390S1 block390S2 block390S3 block390S4

theorem block390RightChunk001ParamsCertificate_eq_true :
    block390RightChunk001ParamsCertificate = true := by
  native_decide

theorem block390_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block390RightChunk001L : ℝ) (block390RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block390S1 : ℝ))
    (hy2ne : y ≠ (block390S2 : ℝ))
    (hy3ne : y ≠ (block390S3 : ℝ))
    (hy4ne : y ≠ (block390S4 : ℝ)) :
    0 < block390V y := by
  have hcert := block390RightChunk001Certificate_eq_true
  unfold block390RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block390RightChunk001) (lo := block390RightChunk001L) (hi := block390RightChunk001R)
    (w1 := block390W1) (w2 := block390W2) (w3 := block390W3) (w4 := block390W4)
    (s1 := block390S1) (s2 := block390S2) (s3 := block390S3) (s4 := block390S4)
    hboxes hcover block390RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block390_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block390RightL : ℝ) (block390RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block390S1 : ℝ))
    (hy2ne : y ≠ (block390S2 : ℝ))
    (hy3ne : y ≠ (block390S3 : ℝ))
    (hy4ne : y ≠ (block390S4 : ℝ)) :
    0 < block390V y := by
  by_cases h0 : y ≤ (block390RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block390RightChunk000L : ℝ) (block390RightChunk000R : ℝ) := by
      have hL : (block390RightChunk000L : ℝ) = (block390RightL : ℝ) := by
        norm_num [block390RightChunk000L, block390RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block390_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block390RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block390RightChunk001L : ℝ) = (block390RightChunk000R : ℝ) := by
      norm_num [block390RightChunk001L, block390RightChunk000R]
    have hR : (block390RightChunk001R : ℝ) = (block390RightR : ℝ) := by
      norm_num [block390RightChunk001R, block390RightR]
    have hyc : y ∈ Icc (block390RightChunk001L : ℝ) (block390RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block390_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block390_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block390LeftL : ℝ) (block390LeftR : ℝ) →
    y ≠ 0 → y ≠ (block390S1 : ℝ) → y ≠ (block390S2 : ℝ) →
    y ≠ (block390S3 : ℝ) → y ≠ (block390S4 : ℝ) → 0 < block390V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block390RightL : ℝ) (block390RightR : ℝ) →
    y ≠ 0 → y ≠ (block390S1 : ℝ) → y ≠ (block390S2 : ℝ) →
    y ≠ (block390S3 : ℝ) → y ≠ (block390S4 : ℝ) → 0 < block390V y)

theorem block390_reallog_certificate_proof :
    block390_reallog_certificate := by
  exact ⟨block390_left_V_pos, block390_right_V_pos⟩

end Block390
end M1817475
end Erdos1038Lean
