from manim import *
from itertools import cycle

def get_sub_indexes(tex):
    ni = VGroup()
    colors = cycle([RED,TEAL,GREEN,BLUE,PURPLE])
    for i in range(len(tex)):
        n = Text(f"{i}",color=next(colors)).scale(0.7)
        n.next_to(tex[i],DOWN,buff=0.01)
        ni.add(n)
        return ni


class Sequents(Scene):

    def construct(self):
        myTemplate = TexTemplate()
        myTemplate.add_to_preamble(r"\usepackage{bussproofs}")
        der1 = r"\AxiomC{$A, B, \Gamma$}\AxiomC{$A, C, \Gamma$}\BinaryInfC{$A, B \wedge C, \Gamma$}\AxiomC{$A^{\perp}, \Delta$}\BinaryInfC{$B \wedge C, \Gamma, \Delta$}\DisplayProof"
        der2 = r"\AxiomC{$A, B, \Gamma$}\AxiomC{$A^{\perp}, \Delta$}\BinaryInfC{$B, \Gamma, \Delta$}\AxiomC{$A, C, \Gamma$}\AxiomC{$A^{\perp}, \Delta$}\BinaryInfC{$C, \Gamma, \Delta$}\BinaryInfC{$B \wedge C, \Gamma, \Delta$}\DisplayProof"
        source = Tex(
            der1,
            tex_template = myTemplate
        )
        target = Tex(
            der2,
            tex_template = myTemplate
        )

        VGroup(source,target)
        self.add(source)


        # VGroup(source,target).arrange(DOWN,buff=2)
        # source_ind = get_sub_indexes(source)
        # target_ind = get_sub_indexes(target)

        # self.add(
        #     source, source_ind,
        #     target, target_ind
        # )

        transform_index = [
            [0, 1, 2, 3, 4, 5,  6,  7,  8,  9,  10, 13, 15, 16, "r16", 17, "r17", 18, 19, 20, 21, "r21", "r21", "r18", "r19", "r20", "r21", 22, "r22", 23, 24, 25, 26, 27, 28, 29],
            [0, 1, 2, 3, 4, 15, 16, 17, 18, 19, 30, 10, 25, 11,  26,   12,  27,   5,  6,  7,  8,   14,    29,    20,    21,    22,    23,   9,   24,   31, 32, 33, 34, 35, 36, 37]
        ]

        # transform_index = [
        #     [0, 1, 2, 3, 4, 5,  6,  7,  8,  9,  10],
        #     [0, 1, 2, 3, 4, 15, 16, 17, 18, 19, 9]
        # ]

        self.play(
            *([
                # Try replacing "ReplacementTransform" with "FadeTransform"
                ReplacementTransform(source[0][i],target[0][j])
                if type(i) is int else
                ReplacementTransform(source[0][int(i[1:])].copy(),target[0][j])
                for i,j in zip(*transform_index)
            ] +
            [
                FadeOut(source[0][11]), FadeOut(source[0][12]), FadeOut(source[0][14]),
                FadeIn(target[0][13]), FadeIn(target[0][28])
            ]),
            run_time=3
        )
        self.wait()


        # self.add(tex1)
        # self.play(Wait(run_time=1))
        # self.play(ChangeSpeed(TransformMatchingShapes(tex1, tex2), speedinfo={0: 0.5, 1: 0.5}))
        # self.play(Wait(run_time=1))
