from z3 import *
import itertools

def main():
    # 使用 Bools 定义多个变量，并确保拆包正确
    power1, power2, power3 = Bools('power1 power2 power3')
    clock1, clock2, clock3 = Bools('clock1 clock2 clock3')
    reset1, reset2, reset3 = Bools('reset1 reset2 reset3')

    # 将所有变量放入列表，方便后续固定赋值和输出
    variables = [power1, power2, power3, clock1, clock2, clock3, reset1, reset2, reset3]

    # 定义基本约束，不含固定赋值部分
    base = Solver()

    # 1. 电源之间的依赖（链式依赖）
    base.add(Implies(power1, power2))
    base.add(Implies(power2, power3))
    base.add(Implies(power3, power1))

    # 2. 时钟之间的依赖：clock1 -> clock2 -> clock3
    base.add(Implies(clock1, clock2))
    base.add(Implies(clock2, clock3))

    # 3. 修改复位之间的约束为 DAG 依赖：
    #    如果 reset1 激活，则 reset2 必须激活；如果 reset2 激活，则 reset3 必须激活
    base.add(Implies(reset1, reset2))
    base.add(Implies(reset2, reset3))

    # 4. 模块内依赖
    groups = [(power1, clock1, reset1),
              (power2, clock2, reset2),
              (power3, clock3, reset3)]
    for p, c, r in groups:
        base.add(Implies(c, p))                 # 如果时钟激活，则电源必须激活
        base.add(Implies(r, p))                 # 如果复位激活，则电源必须激活
        base.add(Implies(r, Not(c)))            # 复位激活时，对应时钟必须关闭
        base.add(Implies(Not(p), And(Not(c), Not(r))))  # 电源关闭，则时钟和复位都关闭

    # 5. 跨模块依赖
    base.add(Implies(reset1, Not(clock2)))  # 模块1的复位激活会导致模块2的时钟关闭
    base.add(Implies(clock3, Not(reset2)))  # 模块3的时钟激活会导致模块2的复位不激活

    # 6. 附加约束：至少有一个电源激活
    base.add(Or(power1, power2, power3))

    # 根据约束分析：
    # 电源只能全开；时钟和复位有几种可能的组合
    power_cases = [(True, True, True)]  # 电源只有一种可能

    clock_cases = [
        (False, False, False),
        (False, False, True),
        (False, True, True),
        (True, True, True)
    ]

    reset_cases = [
        (False, False, False),
        (True, False, False),  # 若 reset1 为 True，根据 DAG 依赖，这个情况不会有解
        (False, True, False),  # 同理，如果 reset2 为 True但 reset1 为 False，违反 reset1->reset2 依赖
        (False, False, True),  # 同理，reset3 单独激活也不符合依赖
        (True, True, False),   # reset1,reset2 激活，但 reset3 未激活，也不满足 reset2->reset3
        (False, True, True),   # 这种情况也不行，因为 reset2 为 True要求 reset1 也为 True
        (True, False, True),   # 这种情况也违反依赖（reset1 为 True要求 reset2 为 True）
        (True, True, True)     # 唯一满足 DAG 依赖的激活情况
    ]

    # 输出表头
    header_vars = ['power1','power2','power3','clock1','clock2','clock3','reset1','reset2','reset3']
    header = " | ".join(header_vars)
    print(header)
    print("-" * len(header))

    total_cases = 0
    solved_cases = 0
    # 枚举所有可能的组合（1 * 4 * len(reset_cases) 组）
    for p_case in power_cases:
        for c_case in clock_cases:
            for r_case in reset_cases:
                total_cases += 1
                # 新建一个 solver，并添加基本约束
                s = Solver()
                s.add(base.assertions())
                # 添加固定赋值约束
                s.add(power1 == p_case[0])
                s.add(power2 == p_case[1])
                s.add(power3 == p_case[2])
                s.add(clock1 == c_case[0])
                s.add(clock2 == c_case[1])
                s.add(clock3 == c_case[2])
                s.add(reset1 == r_case[0])
                s.add(reset2 == r_case[1])
                s.add(reset3 == r_case[2])

                # 检查当前组合是否满足所有约束
                if s.check() == sat:
                    solved_cases += 1
                    vals = p_case + c_case + r_case
                    row = " | ".join(["T" if v else "F" for v in vals])
                    print(row)
                else:
                    row = " | ".join(["X"] * len(variables))
                    print(row)

    print(f"\n总共 {total_cases} 种开关情况，其中 {solved_cases} 种有解。")

if __name__ == '__main__':
    main()
