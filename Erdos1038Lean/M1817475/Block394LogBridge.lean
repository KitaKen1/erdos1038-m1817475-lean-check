import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block394

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block394

open Set

def block394W1 : Rat := ((4004205205387511 : Rat) / 5000000000000000)
def block394W2 : Rat := ((4060358613442341 : Rat) / 100000000000000000)
def block394W3 : Rat := ((3453138019832191 : Rat) / 20000000000000000)
def block394W4 : Rat := ((2919280586064073 : Rat) / 20000000000000000)
def block394S1 : Rat := ((18174751 : Rat) / 10000000)
def block394S2 : Rat := ((511587 : Rat) / 200000)
def block394S3 : Rat := ((26486241803571428583 : Rat) / 10000000000000000000)
def block394S4 : Rat := ((34776808526785713037 : Rat) / 12500000000000000000)

noncomputable def block394V (y : ℝ) : ℝ :=
  ratPotential block394W1 block394W2 block394W3 block394W4 block394S1 block394S2 block394S3 block394S4 y

def block394LeftParamsCertificate : Bool :=
  allBoxesSameParams block394LeftBoxes block394W1 block394W2 block394W3 block394W4 block394S1 block394S2 block394S3 block394S4

theorem block394LeftParamsCertificate_eq_true :
    block394LeftParamsCertificate = true := by
  native_decide

theorem block394_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block394LeftL : ℝ) (block394LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block394S1 : ℝ))
    (hy2ne : y ≠ (block394S2 : ℝ))
    (hy3ne : y ≠ (block394S3 : ℝ))
    (hy4ne : y ≠ (block394S4 : ℝ)) :
    0 < block394V y := by
  have hcert := block394LeftCertificate_eq_true
  unfold block394LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block394LeftBoxes) (lo := block394LeftL) (hi := block394LeftR)
    (w1 := block394W1) (w2 := block394W2) (w3 := block394W3) (w4 := block394W4)
    (s1 := block394S1) (s2 := block394S2) (s3 := block394S3) (s4 := block394S4)
    hboxes hcover block394LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block394RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block394RightChunk000 block394W1 block394W2 block394W3 block394W4 block394S1 block394S2 block394S3 block394S4

theorem block394RightChunk000ParamsCertificate_eq_true :
    block394RightChunk000ParamsCertificate = true := by
  native_decide

theorem block394_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block394RightChunk000L : ℝ) (block394RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block394S1 : ℝ))
    (hy2ne : y ≠ (block394S2 : ℝ))
    (hy3ne : y ≠ (block394S3 : ℝ))
    (hy4ne : y ≠ (block394S4 : ℝ)) :
    0 < block394V y := by
  have hcert := block394RightChunk000Certificate_eq_true
  unfold block394RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block394RightChunk000) (lo := block394RightChunk000L) (hi := block394RightChunk000R)
    (w1 := block394W1) (w2 := block394W2) (w3 := block394W3) (w4 := block394W4)
    (s1 := block394S1) (s2 := block394S2) (s3 := block394S3) (s4 := block394S4)
    hboxes hcover block394RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block394RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block394RightChunk001 block394W1 block394W2 block394W3 block394W4 block394S1 block394S2 block394S3 block394S4

theorem block394RightChunk001ParamsCertificate_eq_true :
    block394RightChunk001ParamsCertificate = true := by
  native_decide

theorem block394_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block394RightChunk001L : ℝ) (block394RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block394S1 : ℝ))
    (hy2ne : y ≠ (block394S2 : ℝ))
    (hy3ne : y ≠ (block394S3 : ℝ))
    (hy4ne : y ≠ (block394S4 : ℝ)) :
    0 < block394V y := by
  have hcert := block394RightChunk001Certificate_eq_true
  unfold block394RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block394RightChunk001) (lo := block394RightChunk001L) (hi := block394RightChunk001R)
    (w1 := block394W1) (w2 := block394W2) (w3 := block394W3) (w4 := block394W4)
    (s1 := block394S1) (s2 := block394S2) (s3 := block394S3) (s4 := block394S4)
    hboxes hcover block394RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block394_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block394RightL : ℝ) (block394RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block394S1 : ℝ))
    (hy2ne : y ≠ (block394S2 : ℝ))
    (hy3ne : y ≠ (block394S3 : ℝ))
    (hy4ne : y ≠ (block394S4 : ℝ)) :
    0 < block394V y := by
  by_cases h0 : y ≤ (block394RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block394RightChunk000L : ℝ) (block394RightChunk000R : ℝ) := by
      have hL : (block394RightChunk000L : ℝ) = (block394RightL : ℝ) := by
        norm_num [block394RightChunk000L, block394RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block394_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block394RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block394RightChunk001L : ℝ) = (block394RightChunk000R : ℝ) := by
      norm_num [block394RightChunk001L, block394RightChunk000R]
    have hR : (block394RightChunk001R : ℝ) = (block394RightR : ℝ) := by
      norm_num [block394RightChunk001R, block394RightR]
    have hyc : y ∈ Icc (block394RightChunk001L : ℝ) (block394RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block394_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block394_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block394LeftL : ℝ) (block394LeftR : ℝ) →
    y ≠ 0 → y ≠ (block394S1 : ℝ) → y ≠ (block394S2 : ℝ) →
    y ≠ (block394S3 : ℝ) → y ≠ (block394S4 : ℝ) → 0 < block394V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block394RightL : ℝ) (block394RightR : ℝ) →
    y ≠ 0 → y ≠ (block394S1 : ℝ) → y ≠ (block394S2 : ℝ) →
    y ≠ (block394S3 : ℝ) → y ≠ (block394S4 : ℝ) → 0 < block394V y)

theorem block394_reallog_certificate_proof :
    block394_reallog_certificate := by
  exact ⟨block394_left_V_pos, block394_right_V_pos⟩

end Block394
end M1817475
end Erdos1038Lean
