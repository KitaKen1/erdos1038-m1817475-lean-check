import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block391

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block391

open Set

def block391W1 : Rat := ((2012592833678559 : Rat) / 2500000000000000)
def block391W2 : Rat := ((1029658521475993 : Rat) / 25000000000000000)
def block391W3 : Rat := ((8568424433031617 : Rat) / 50000000000000000)
def block391W4 : Rat := ((364483008932439 : Rat) / 2500000000000000)
def block391S1 : Rat := ((18174751 : Rat) / 10000000)
def block391S2 : Rat := ((511587 : Rat) / 200000)
def block391S3 : Rat := ((132489856339285714341 : Rat) / 50000000000000000000)
def block391S4 : Rat := ((34776808526785713037 : Rat) / 12500000000000000000)

noncomputable def block391V (y : ℝ) : ℝ :=
  ratPotential block391W1 block391W2 block391W3 block391W4 block391S1 block391S2 block391S3 block391S4 y

def block391LeftParamsCertificate : Bool :=
  allBoxesSameParams block391LeftBoxes block391W1 block391W2 block391W3 block391W4 block391S1 block391S2 block391S3 block391S4

theorem block391LeftParamsCertificate_eq_true :
    block391LeftParamsCertificate = true := by
  native_decide

theorem block391_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block391LeftL : ℝ) (block391LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block391S1 : ℝ))
    (hy2ne : y ≠ (block391S2 : ℝ))
    (hy3ne : y ≠ (block391S3 : ℝ))
    (hy4ne : y ≠ (block391S4 : ℝ)) :
    0 < block391V y := by
  have hcert := block391LeftCertificate_eq_true
  unfold block391LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block391LeftBoxes) (lo := block391LeftL) (hi := block391LeftR)
    (w1 := block391W1) (w2 := block391W2) (w3 := block391W3) (w4 := block391W4)
    (s1 := block391S1) (s2 := block391S2) (s3 := block391S3) (s4 := block391S4)
    hboxes hcover block391LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block391RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block391RightChunk000 block391W1 block391W2 block391W3 block391W4 block391S1 block391S2 block391S3 block391S4

theorem block391RightChunk000ParamsCertificate_eq_true :
    block391RightChunk000ParamsCertificate = true := by
  native_decide

theorem block391_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block391RightChunk000L : ℝ) (block391RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block391S1 : ℝ))
    (hy2ne : y ≠ (block391S2 : ℝ))
    (hy3ne : y ≠ (block391S3 : ℝ))
    (hy4ne : y ≠ (block391S4 : ℝ)) :
    0 < block391V y := by
  have hcert := block391RightChunk000Certificate_eq_true
  unfold block391RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block391RightChunk000) (lo := block391RightChunk000L) (hi := block391RightChunk000R)
    (w1 := block391W1) (w2 := block391W2) (w3 := block391W3) (w4 := block391W4)
    (s1 := block391S1) (s2 := block391S2) (s3 := block391S3) (s4 := block391S4)
    hboxes hcover block391RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block391RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block391RightChunk001 block391W1 block391W2 block391W3 block391W4 block391S1 block391S2 block391S3 block391S4

theorem block391RightChunk001ParamsCertificate_eq_true :
    block391RightChunk001ParamsCertificate = true := by
  native_decide

theorem block391_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block391RightChunk001L : ℝ) (block391RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block391S1 : ℝ))
    (hy2ne : y ≠ (block391S2 : ℝ))
    (hy3ne : y ≠ (block391S3 : ℝ))
    (hy4ne : y ≠ (block391S4 : ℝ)) :
    0 < block391V y := by
  have hcert := block391RightChunk001Certificate_eq_true
  unfold block391RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block391RightChunk001) (lo := block391RightChunk001L) (hi := block391RightChunk001R)
    (w1 := block391W1) (w2 := block391W2) (w3 := block391W3) (w4 := block391W4)
    (s1 := block391S1) (s2 := block391S2) (s3 := block391S3) (s4 := block391S4)
    hboxes hcover block391RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block391_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block391RightL : ℝ) (block391RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block391S1 : ℝ))
    (hy2ne : y ≠ (block391S2 : ℝ))
    (hy3ne : y ≠ (block391S3 : ℝ))
    (hy4ne : y ≠ (block391S4 : ℝ)) :
    0 < block391V y := by
  by_cases h0 : y ≤ (block391RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block391RightChunk000L : ℝ) (block391RightChunk000R : ℝ) := by
      have hL : (block391RightChunk000L : ℝ) = (block391RightL : ℝ) := by
        norm_num [block391RightChunk000L, block391RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block391_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block391RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block391RightChunk001L : ℝ) = (block391RightChunk000R : ℝ) := by
      norm_num [block391RightChunk001L, block391RightChunk000R]
    have hR : (block391RightChunk001R : ℝ) = (block391RightR : ℝ) := by
      norm_num [block391RightChunk001R, block391RightR]
    have hyc : y ∈ Icc (block391RightChunk001L : ℝ) (block391RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block391_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block391_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block391LeftL : ℝ) (block391LeftR : ℝ) →
    y ≠ 0 → y ≠ (block391S1 : ℝ) → y ≠ (block391S2 : ℝ) →
    y ≠ (block391S3 : ℝ) → y ≠ (block391S4 : ℝ) → 0 < block391V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block391RightL : ℝ) (block391RightR : ℝ) →
    y ≠ 0 → y ≠ (block391S1 : ℝ) → y ≠ (block391S2 : ℝ) →
    y ≠ (block391S3 : ℝ) → y ≠ (block391S4 : ℝ) → 0 < block391V y)

theorem block391_reallog_certificate_proof :
    block391_reallog_certificate := by
  exact ⟨block391_left_V_pos, block391_right_V_pos⟩

end Block391
end M1817475
end Erdos1038Lean
