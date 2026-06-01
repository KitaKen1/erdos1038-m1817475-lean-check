import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block387

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block387

open Set

def block387W1 : Rat := ((2028786654113631 : Rat) / 2500000000000000)
def block387W2 : Rat := ((8328557505500353 : Rat) / 200000000000000000)
def block387W3 : Rat := ((16983677385250737 : Rat) / 100000000000000000)
def block387W4 : Rat := ((7278969627828903 : Rat) / 50000000000000000)
def block387S1 : Rat := ((18174751 : Rat) / 10000000)
def block387S2 : Rat := ((511587 : Rat) / 200000)
def block387S3 : Rat := ((132568052767857142909 : Rat) / 50000000000000000000)
def block387S4 : Rat := ((34776808526785713037 : Rat) / 12500000000000000000)

noncomputable def block387V (y : ℝ) : ℝ :=
  ratPotential block387W1 block387W2 block387W3 block387W4 block387S1 block387S2 block387S3 block387S4 y

def block387LeftParamsCertificate : Bool :=
  allBoxesSameParams block387LeftBoxes block387W1 block387W2 block387W3 block387W4 block387S1 block387S2 block387S3 block387S4

theorem block387LeftParamsCertificate_eq_true :
    block387LeftParamsCertificate = true := by
  native_decide

theorem block387_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block387LeftL : ℝ) (block387LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block387S1 : ℝ))
    (hy2ne : y ≠ (block387S2 : ℝ))
    (hy3ne : y ≠ (block387S3 : ℝ))
    (hy4ne : y ≠ (block387S4 : ℝ)) :
    0 < block387V y := by
  have hcert := block387LeftCertificate_eq_true
  unfold block387LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block387LeftBoxes) (lo := block387LeftL) (hi := block387LeftR)
    (w1 := block387W1) (w2 := block387W2) (w3 := block387W3) (w4 := block387W4)
    (s1 := block387S1) (s2 := block387S2) (s3 := block387S3) (s4 := block387S4)
    hboxes hcover block387LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block387RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block387RightChunk000 block387W1 block387W2 block387W3 block387W4 block387S1 block387S2 block387S3 block387S4

theorem block387RightChunk000ParamsCertificate_eq_true :
    block387RightChunk000ParamsCertificate = true := by
  native_decide

theorem block387_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block387RightChunk000L : ℝ) (block387RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block387S1 : ℝ))
    (hy2ne : y ≠ (block387S2 : ℝ))
    (hy3ne : y ≠ (block387S3 : ℝ))
    (hy4ne : y ≠ (block387S4 : ℝ)) :
    0 < block387V y := by
  have hcert := block387RightChunk000Certificate_eq_true
  unfold block387RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block387RightChunk000) (lo := block387RightChunk000L) (hi := block387RightChunk000R)
    (w1 := block387W1) (w2 := block387W2) (w3 := block387W3) (w4 := block387W4)
    (s1 := block387S1) (s2 := block387S2) (s3 := block387S3) (s4 := block387S4)
    hboxes hcover block387RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block387RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block387RightChunk001 block387W1 block387W2 block387W3 block387W4 block387S1 block387S2 block387S3 block387S4

theorem block387RightChunk001ParamsCertificate_eq_true :
    block387RightChunk001ParamsCertificate = true := by
  native_decide

theorem block387_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block387RightChunk001L : ℝ) (block387RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block387S1 : ℝ))
    (hy2ne : y ≠ (block387S2 : ℝ))
    (hy3ne : y ≠ (block387S3 : ℝ))
    (hy4ne : y ≠ (block387S4 : ℝ)) :
    0 < block387V y := by
  have hcert := block387RightChunk001Certificate_eq_true
  unfold block387RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block387RightChunk001) (lo := block387RightChunk001L) (hi := block387RightChunk001R)
    (w1 := block387W1) (w2 := block387W2) (w3 := block387W3) (w4 := block387W4)
    (s1 := block387S1) (s2 := block387S2) (s3 := block387S3) (s4 := block387S4)
    hboxes hcover block387RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block387_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block387RightL : ℝ) (block387RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block387S1 : ℝ))
    (hy2ne : y ≠ (block387S2 : ℝ))
    (hy3ne : y ≠ (block387S3 : ℝ))
    (hy4ne : y ≠ (block387S4 : ℝ)) :
    0 < block387V y := by
  by_cases h0 : y ≤ (block387RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block387RightChunk000L : ℝ) (block387RightChunk000R : ℝ) := by
      have hL : (block387RightChunk000L : ℝ) = (block387RightL : ℝ) := by
        norm_num [block387RightChunk000L, block387RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block387_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block387RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block387RightChunk001L : ℝ) = (block387RightChunk000R : ℝ) := by
      norm_num [block387RightChunk001L, block387RightChunk000R]
    have hR : (block387RightChunk001R : ℝ) = (block387RightR : ℝ) := by
      norm_num [block387RightChunk001R, block387RightR]
    have hyc : y ∈ Icc (block387RightChunk001L : ℝ) (block387RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block387_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block387_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block387LeftL : ℝ) (block387LeftR : ℝ) →
    y ≠ 0 → y ≠ (block387S1 : ℝ) → y ≠ (block387S2 : ℝ) →
    y ≠ (block387S3 : ℝ) → y ≠ (block387S4 : ℝ) → 0 < block387V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block387RightL : ℝ) (block387RightR : ℝ) →
    y ≠ 0 → y ≠ (block387S1 : ℝ) → y ≠ (block387S2 : ℝ) →
    y ≠ (block387S3 : ℝ) → y ≠ (block387S4 : ℝ) → 0 < block387V y)

theorem block387_reallog_certificate_proof :
    block387_reallog_certificate := by
  exact ⟨block387_left_V_pos, block387_right_V_pos⟩

end Block387
end M1817475
end Erdos1038Lean
