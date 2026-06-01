import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block239

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block239

open Set

def block239W1 : Rat := ((1727822961664041 : Rat) / 2000000000000000)
def block239W2 : Rat := ((67261101171891 : Rat) / 800000000000000)
def block239W3 : Rat := ((72680253053227 : Rat) / 400000000000000)
def block239W4 : Rat := ((1771288361231809 : Rat) / 25000000000000000)
def block239S1 : Rat := ((18174751 : Rat) / 10000000)
def block239S2 : Rat := ((511587 : Rat) / 200000)
def block239S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block239S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block239V (y : ℝ) : ℝ :=
  ratPotential block239W1 block239W2 block239W3 block239W4 block239S1 block239S2 block239S3 block239S4 y

def block239LeftParamsCertificate : Bool :=
  allBoxesSameParams block239LeftBoxes block239W1 block239W2 block239W3 block239W4 block239S1 block239S2 block239S3 block239S4

theorem block239LeftParamsCertificate_eq_true :
    block239LeftParamsCertificate = true := by
  native_decide

theorem block239_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block239LeftL : ℝ) (block239LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block239S1 : ℝ))
    (hy2ne : y ≠ (block239S2 : ℝ))
    (hy3ne : y ≠ (block239S3 : ℝ))
    (hy4ne : y ≠ (block239S4 : ℝ)) :
    0 < block239V y := by
  have hcert := block239LeftCertificate_eq_true
  unfold block239LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block239LeftBoxes) (lo := block239LeftL) (hi := block239LeftR)
    (w1 := block239W1) (w2 := block239W2) (w3 := block239W3) (w4 := block239W4)
    (s1 := block239S1) (s2 := block239S2) (s3 := block239S3) (s4 := block239S4)
    hboxes hcover block239LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block239RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block239RightChunk000 block239W1 block239W2 block239W3 block239W4 block239S1 block239S2 block239S3 block239S4

theorem block239RightChunk000ParamsCertificate_eq_true :
    block239RightChunk000ParamsCertificate = true := by
  native_decide

theorem block239_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block239RightChunk000L : ℝ) (block239RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block239S1 : ℝ))
    (hy2ne : y ≠ (block239S2 : ℝ))
    (hy3ne : y ≠ (block239S3 : ℝ))
    (hy4ne : y ≠ (block239S4 : ℝ)) :
    0 < block239V y := by
  have hcert := block239RightChunk000Certificate_eq_true
  unfold block239RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block239RightChunk000) (lo := block239RightChunk000L) (hi := block239RightChunk000R)
    (w1 := block239W1) (w2 := block239W2) (w3 := block239W3) (w4 := block239W4)
    (s1 := block239S1) (s2 := block239S2) (s3 := block239S3) (s4 := block239S4)
    hboxes hcover block239RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block239RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block239RightChunk001 block239W1 block239W2 block239W3 block239W4 block239S1 block239S2 block239S3 block239S4

theorem block239RightChunk001ParamsCertificate_eq_true :
    block239RightChunk001ParamsCertificate = true := by
  native_decide

theorem block239_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block239RightChunk001L : ℝ) (block239RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block239S1 : ℝ))
    (hy2ne : y ≠ (block239S2 : ℝ))
    (hy3ne : y ≠ (block239S3 : ℝ))
    (hy4ne : y ≠ (block239S4 : ℝ)) :
    0 < block239V y := by
  have hcert := block239RightChunk001Certificate_eq_true
  unfold block239RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block239RightChunk001) (lo := block239RightChunk001L) (hi := block239RightChunk001R)
    (w1 := block239W1) (w2 := block239W2) (w3 := block239W3) (w4 := block239W4)
    (s1 := block239S1) (s2 := block239S2) (s3 := block239S3) (s4 := block239S4)
    hboxes hcover block239RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block239_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block239RightL : ℝ) (block239RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block239S1 : ℝ))
    (hy2ne : y ≠ (block239S2 : ℝ))
    (hy3ne : y ≠ (block239S3 : ℝ))
    (hy4ne : y ≠ (block239S4 : ℝ)) :
    0 < block239V y := by
  by_cases h0 : y ≤ (block239RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block239RightChunk000L : ℝ) (block239RightChunk000R : ℝ) := by
      have hL : (block239RightChunk000L : ℝ) = (block239RightL : ℝ) := by
        norm_num [block239RightChunk000L, block239RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block239_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block239RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block239RightChunk001L : ℝ) = (block239RightChunk000R : ℝ) := by
      norm_num [block239RightChunk001L, block239RightChunk000R]
    have hR : (block239RightChunk001R : ℝ) = (block239RightR : ℝ) := by
      norm_num [block239RightChunk001R, block239RightR]
    have hyc : y ∈ Icc (block239RightChunk001L : ℝ) (block239RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block239_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block239_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block239LeftL : ℝ) (block239LeftR : ℝ) →
    y ≠ 0 → y ≠ (block239S1 : ℝ) → y ≠ (block239S2 : ℝ) →
    y ≠ (block239S3 : ℝ) → y ≠ (block239S4 : ℝ) → 0 < block239V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block239RightL : ℝ) (block239RightR : ℝ) →
    y ≠ 0 → y ≠ (block239S1 : ℝ) → y ≠ (block239S2 : ℝ) →
    y ≠ (block239S3 : ℝ) → y ≠ (block239S4 : ℝ) → 0 < block239V y)

theorem block239_reallog_certificate_proof :
    block239_reallog_certificate := by
  exact ⟨block239_left_V_pos, block239_right_V_pos⟩

end Block239
end M1817475
end Erdos1038Lean
