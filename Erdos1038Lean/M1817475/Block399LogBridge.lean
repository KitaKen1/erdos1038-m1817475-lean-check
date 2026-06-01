import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block399

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block399

open Set

def block399W1 : Rat := ((235656598363987 : Rat) / 312500000000000)
def block399W2 : Rat := (0 : Rat)
def block399W3 : Rat := ((6888206723906229 : Rat) / 25000000000000000)
def block399W4 : Rat := ((2350609299220293 : Rat) / 25000000000000000)
def block399S1 : Rat := ((18174751 : Rat) / 10000000)
def block399S2 : Rat := ((511587 : Rat) / 200000)
def block399S3 : Rat := ((26466692696428571441 : Rat) / 10000000000000000000)
def block399S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block399V (y : ℝ) : ℝ :=
  ratPotential block399W1 block399W2 block399W3 block399W4 block399S1 block399S2 block399S3 block399S4 y

def block399LeftParamsCertificate : Bool :=
  allBoxesSameParams block399LeftBoxes block399W1 block399W2 block399W3 block399W4 block399S1 block399S2 block399S3 block399S4

theorem block399LeftParamsCertificate_eq_true :
    block399LeftParamsCertificate = true := by
  native_decide

theorem block399_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block399LeftL : ℝ) (block399LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block399S1 : ℝ))
    (hy2ne : y ≠ (block399S2 : ℝ))
    (hy3ne : y ≠ (block399S3 : ℝ))
    (hy4ne : y ≠ (block399S4 : ℝ)) :
    0 < block399V y := by
  have hcert := block399LeftCertificate_eq_true
  unfold block399LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block399LeftBoxes) (lo := block399LeftL) (hi := block399LeftR)
    (w1 := block399W1) (w2 := block399W2) (w3 := block399W3) (w4 := block399W4)
    (s1 := block399S1) (s2 := block399S2) (s3 := block399S3) (s4 := block399S4)
    hboxes hcover block399LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block399RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block399RightChunk000 block399W1 block399W2 block399W3 block399W4 block399S1 block399S2 block399S3 block399S4

theorem block399RightChunk000ParamsCertificate_eq_true :
    block399RightChunk000ParamsCertificate = true := by
  native_decide

theorem block399_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block399RightChunk000L : ℝ) (block399RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block399S1 : ℝ))
    (hy2ne : y ≠ (block399S2 : ℝ))
    (hy3ne : y ≠ (block399S3 : ℝ))
    (hy4ne : y ≠ (block399S4 : ℝ)) :
    0 < block399V y := by
  have hcert := block399RightChunk000Certificate_eq_true
  unfold block399RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block399RightChunk000) (lo := block399RightChunk000L) (hi := block399RightChunk000R)
    (w1 := block399W1) (w2 := block399W2) (w3 := block399W3) (w4 := block399W4)
    (s1 := block399S1) (s2 := block399S2) (s3 := block399S3) (s4 := block399S4)
    hboxes hcover block399RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block399RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block399RightChunk001 block399W1 block399W2 block399W3 block399W4 block399S1 block399S2 block399S3 block399S4

theorem block399RightChunk001ParamsCertificate_eq_true :
    block399RightChunk001ParamsCertificate = true := by
  native_decide

theorem block399_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block399RightChunk001L : ℝ) (block399RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block399S1 : ℝ))
    (hy2ne : y ≠ (block399S2 : ℝ))
    (hy3ne : y ≠ (block399S3 : ℝ))
    (hy4ne : y ≠ (block399S4 : ℝ)) :
    0 < block399V y := by
  have hcert := block399RightChunk001Certificate_eq_true
  unfold block399RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block399RightChunk001) (lo := block399RightChunk001L) (hi := block399RightChunk001R)
    (w1 := block399W1) (w2 := block399W2) (w3 := block399W3) (w4 := block399W4)
    (s1 := block399S1) (s2 := block399S2) (s3 := block399S3) (s4 := block399S4)
    hboxes hcover block399RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block399RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block399RightChunk002 block399W1 block399W2 block399W3 block399W4 block399S1 block399S2 block399S3 block399S4

theorem block399RightChunk002ParamsCertificate_eq_true :
    block399RightChunk002ParamsCertificate = true := by
  native_decide

theorem block399_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block399RightChunk002L : ℝ) (block399RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block399S1 : ℝ))
    (hy2ne : y ≠ (block399S2 : ℝ))
    (hy3ne : y ≠ (block399S3 : ℝ))
    (hy4ne : y ≠ (block399S4 : ℝ)) :
    0 < block399V y := by
  have hcert := block399RightChunk002Certificate_eq_true
  unfold block399RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block399RightChunk002) (lo := block399RightChunk002L) (hi := block399RightChunk002R)
    (w1 := block399W1) (w2 := block399W2) (w3 := block399W3) (w4 := block399W4)
    (s1 := block399S1) (s2 := block399S2) (s3 := block399S3) (s4 := block399S4)
    hboxes hcover block399RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block399RightChunk003ParamsCertificate : Bool :=
  allBoxesSameParams block399RightChunk003 block399W1 block399W2 block399W3 block399W4 block399S1 block399S2 block399S3 block399S4

theorem block399RightChunk003ParamsCertificate_eq_true :
    block399RightChunk003ParamsCertificate = true := by
  native_decide

theorem block399_right_chunk003_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block399RightChunk003L : ℝ) (block399RightChunk003R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block399S1 : ℝ))
    (hy2ne : y ≠ (block399S2 : ℝ))
    (hy3ne : y ≠ (block399S3 : ℝ))
    (hy4ne : y ≠ (block399S4 : ℝ)) :
    0 < block399V y := by
  have hcert := block399RightChunk003Certificate_eq_true
  unfold block399RightChunk003Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block399RightChunk003) (lo := block399RightChunk003L) (hi := block399RightChunk003R)
    (w1 := block399W1) (w2 := block399W2) (w3 := block399W3) (w4 := block399W4)
    (s1 := block399S1) (s2 := block399S2) (s3 := block399S3) (s4 := block399S4)
    hboxes hcover block399RightChunk003ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block399RightChunk004ParamsCertificate : Bool :=
  allBoxesSameParams block399RightChunk004 block399W1 block399W2 block399W3 block399W4 block399S1 block399S2 block399S3 block399S4

theorem block399RightChunk004ParamsCertificate_eq_true :
    block399RightChunk004ParamsCertificate = true := by
  native_decide

theorem block399_right_chunk004_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block399RightChunk004L : ℝ) (block399RightChunk004R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block399S1 : ℝ))
    (hy2ne : y ≠ (block399S2 : ℝ))
    (hy3ne : y ≠ (block399S3 : ℝ))
    (hy4ne : y ≠ (block399S4 : ℝ)) :
    0 < block399V y := by
  have hcert := block399RightChunk004Certificate_eq_true
  unfold block399RightChunk004Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block399RightChunk004) (lo := block399RightChunk004L) (hi := block399RightChunk004R)
    (w1 := block399W1) (w2 := block399W2) (w3 := block399W3) (w4 := block399W4)
    (s1 := block399S1) (s2 := block399S2) (s3 := block399S3) (s4 := block399S4)
    hboxes hcover block399RightChunk004ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block399RightChunk005ParamsCertificate : Bool :=
  allBoxesSameParams block399RightChunk005 block399W1 block399W2 block399W3 block399W4 block399S1 block399S2 block399S3 block399S4

theorem block399RightChunk005ParamsCertificate_eq_true :
    block399RightChunk005ParamsCertificate = true := by
  native_decide

theorem block399_right_chunk005_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block399RightChunk005L : ℝ) (block399RightChunk005R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block399S1 : ℝ))
    (hy2ne : y ≠ (block399S2 : ℝ))
    (hy3ne : y ≠ (block399S3 : ℝ))
    (hy4ne : y ≠ (block399S4 : ℝ)) :
    0 < block399V y := by
  have hcert := block399RightChunk005Certificate_eq_true
  unfold block399RightChunk005Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block399RightChunk005) (lo := block399RightChunk005L) (hi := block399RightChunk005R)
    (w1 := block399W1) (w2 := block399W2) (w3 := block399W3) (w4 := block399W4)
    (s1 := block399S1) (s2 := block399S2) (s3 := block399S3) (s4 := block399S4)
    hboxes hcover block399RightChunk005ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block399RightChunk006ParamsCertificate : Bool :=
  allBoxesSameParams block399RightChunk006 block399W1 block399W2 block399W3 block399W4 block399S1 block399S2 block399S3 block399S4

theorem block399RightChunk006ParamsCertificate_eq_true :
    block399RightChunk006ParamsCertificate = true := by
  native_decide

theorem block399_right_chunk006_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block399RightChunk006L : ℝ) (block399RightChunk006R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block399S1 : ℝ))
    (hy2ne : y ≠ (block399S2 : ℝ))
    (hy3ne : y ≠ (block399S3 : ℝ))
    (hy4ne : y ≠ (block399S4 : ℝ)) :
    0 < block399V y := by
  have hcert := block399RightChunk006Certificate_eq_true
  unfold block399RightChunk006Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block399RightChunk006) (lo := block399RightChunk006L) (hi := block399RightChunk006R)
    (w1 := block399W1) (w2 := block399W2) (w3 := block399W3) (w4 := block399W4)
    (s1 := block399S1) (s2 := block399S2) (s3 := block399S3) (s4 := block399S4)
    hboxes hcover block399RightChunk006ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block399RightChunk007ParamsCertificate : Bool :=
  allBoxesSameParams block399RightChunk007 block399W1 block399W2 block399W3 block399W4 block399S1 block399S2 block399S3 block399S4

theorem block399RightChunk007ParamsCertificate_eq_true :
    block399RightChunk007ParamsCertificate = true := by
  native_decide

theorem block399_right_chunk007_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block399RightChunk007L : ℝ) (block399RightChunk007R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block399S1 : ℝ))
    (hy2ne : y ≠ (block399S2 : ℝ))
    (hy3ne : y ≠ (block399S3 : ℝ))
    (hy4ne : y ≠ (block399S4 : ℝ)) :
    0 < block399V y := by
  have hcert := block399RightChunk007Certificate_eq_true
  unfold block399RightChunk007Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block399RightChunk007) (lo := block399RightChunk007L) (hi := block399RightChunk007R)
    (w1 := block399W1) (w2 := block399W2) (w3 := block399W3) (w4 := block399W4)
    (s1 := block399S1) (s2 := block399S2) (s3 := block399S3) (s4 := block399S4)
    hboxes hcover block399RightChunk007ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block399_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block399RightL : ℝ) (block399RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block399S1 : ℝ))
    (hy2ne : y ≠ (block399S2 : ℝ))
    (hy3ne : y ≠ (block399S3 : ℝ))
    (hy4ne : y ≠ (block399S4 : ℝ)) :
    0 < block399V y := by
  by_cases h0 : y ≤ (block399RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block399RightChunk000L : ℝ) (block399RightChunk000R : ℝ) := by
      have hL : (block399RightChunk000L : ℝ) = (block399RightL : ℝ) := by
        norm_num [block399RightChunk000L, block399RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block399_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block399RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block399RightChunk001L : ℝ) (block399RightChunk001R : ℝ) := by
        have hprev : (block399RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block399RightChunk001L : ℝ) = (block399RightChunk000R : ℝ) := by
          norm_num [block399RightChunk001L, block399RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block399_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      by_cases h2 : y ≤ (block399RightChunk002R : ℝ)
      · have hyc : y ∈ Icc (block399RightChunk002L : ℝ) (block399RightChunk002R : ℝ) := by
          have hprev : (block399RightChunk001R : ℝ) < y := lt_of_not_ge h1
          have hL : (block399RightChunk002L : ℝ) = (block399RightChunk001R : ℝ) := by
            norm_num [block399RightChunk002L, block399RightChunk001R]
          constructor
          · linarith [hprev, hL]
          · exact h2
        exact block399_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
      ·
        by_cases h3 : y ≤ (block399RightChunk003R : ℝ)
        · have hyc : y ∈ Icc (block399RightChunk003L : ℝ) (block399RightChunk003R : ℝ) := by
            have hprev : (block399RightChunk002R : ℝ) < y := lt_of_not_ge h2
            have hL : (block399RightChunk003L : ℝ) = (block399RightChunk002R : ℝ) := by
              norm_num [block399RightChunk003L, block399RightChunk002R]
            constructor
            · linarith [hprev, hL]
            · exact h3
          exact block399_right_chunk003_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
        ·
          by_cases h4 : y ≤ (block399RightChunk004R : ℝ)
          · have hyc : y ∈ Icc (block399RightChunk004L : ℝ) (block399RightChunk004R : ℝ) := by
              have hprev : (block399RightChunk003R : ℝ) < y := lt_of_not_ge h3
              have hL : (block399RightChunk004L : ℝ) = (block399RightChunk003R : ℝ) := by
                norm_num [block399RightChunk004L, block399RightChunk003R]
              constructor
              · linarith [hprev, hL]
              · exact h4
            exact block399_right_chunk004_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
          ·
            by_cases h5 : y ≤ (block399RightChunk005R : ℝ)
            · have hyc : y ∈ Icc (block399RightChunk005L : ℝ) (block399RightChunk005R : ℝ) := by
                have hprev : (block399RightChunk004R : ℝ) < y := lt_of_not_ge h4
                have hL : (block399RightChunk005L : ℝ) = (block399RightChunk004R : ℝ) := by
                  norm_num [block399RightChunk005L, block399RightChunk004R]
                constructor
                · linarith [hprev, hL]
                · exact h5
              exact block399_right_chunk005_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
            ·
              by_cases h6 : y ≤ (block399RightChunk006R : ℝ)
              · have hyc : y ∈ Icc (block399RightChunk006L : ℝ) (block399RightChunk006R : ℝ) := by
                  have hprev : (block399RightChunk005R : ℝ) < y := lt_of_not_ge h5
                  have hL : (block399RightChunk006L : ℝ) = (block399RightChunk005R : ℝ) := by
                    norm_num [block399RightChunk006L, block399RightChunk005R]
                  constructor
                  · linarith [hprev, hL]
                  · exact h6
                exact block399_right_chunk006_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
              ·
                have hprev : (block399RightChunk006R : ℝ) < y := lt_of_not_ge h6
                have hL : (block399RightChunk007L : ℝ) = (block399RightChunk006R : ℝ) := by
                  norm_num [block399RightChunk007L, block399RightChunk006R]
                have hR : (block399RightChunk007R : ℝ) = (block399RightR : ℝ) := by
                  norm_num [block399RightChunk007R, block399RightR]
                have hyc : y ∈ Icc (block399RightChunk007L : ℝ) (block399RightChunk007R : ℝ) := by
                  constructor
                  · linarith [hprev, hL]
                  · linarith [hy.2, hR]
                exact block399_right_chunk007_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block399_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block399LeftL : ℝ) (block399LeftR : ℝ) →
    y ≠ 0 → y ≠ (block399S1 : ℝ) → y ≠ (block399S2 : ℝ) →
    y ≠ (block399S3 : ℝ) → y ≠ (block399S4 : ℝ) → 0 < block399V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block399RightL : ℝ) (block399RightR : ℝ) →
    y ≠ 0 → y ≠ (block399S1 : ℝ) → y ≠ (block399S2 : ℝ) →
    y ≠ (block399S3 : ℝ) → y ≠ (block399S4 : ℝ) → 0 < block399V y)

theorem block399_reallog_certificate_proof :
    block399_reallog_certificate := by
  exact ⟨block399_left_V_pos, block399_right_V_pos⟩

end Block399
end M1817475
end Erdos1038Lean
