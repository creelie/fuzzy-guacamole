# Exhaustive search for well-formed weighted projective 4-spaces P(a1,...,a5)
# with canonical singularities and Fano index q = a1+...+a5.
#
# This program uses the symmetric form of Kasprzyk's criterion: P(a) is not
# canonical iff some k in [2, q-2] has k*a_i not divisible by q for every i
# and sum_i (k*a_i mod q) = q.  (Replacing k by q-k turns this into
# age(q-k) = 4, the form used by the C and Python programs.)
#
# Usage: julia -t <threads> wps_search.jl q

function noncanonical(a::NTuple{5,Int}, q::Int)
    @inbounds for k in 2:q-2
        s = 0
        zero = false
        for i in 1:5
            r = (k * a[i]) % q
            if r == 0
                zero = true
                break
            end
            s += r
            s > q && break
        end
        (!zero && s == q) && return true
    end
    return false
end

function wellformed(a::NTuple{5,Int})
    for i in 1:5
        g = 0
        for j in 1:5
            j == i || (g = gcd(g, a[j]))
        end
        g == 1 || return false
    end
    return true
end

function search(q::Int)
    # a1 >= a2 >= a3 >= a4 >= a5 >= 1, sum q; threads split on the largest weight a1.
    a1s = collect(cld(q, 5):q-4)
    nt = Threads.nthreads()
    tup = zeros(Int, length(a1s)); wf = zeros(Int, length(a1s))
    found = [NTuple{5,Int}[] for _ in a1s]
    Threads.@threads :dynamic for idx in eachindex(a1s)
        a1 = a1s[idx]
        t = 0; w = 0
        for a2 in min(a1, q - a1 - 3):-1:1
            r2 = q - a1 - a2
            4 * a2 < q - a1 && break
            for a3 in min(a2, r2 - 2):-1:1
                r3 = r2 - a3
                3 * a3 < r2 && break
                for a4 in min(a3, r3 - 1):-1:1
                    a5 = r3 - a4
                    a5 > a4 && break
                    t += 1
                    a = (a1, a2, a3, a4, a5)
                    wellformed(a) || continue
                    w += 1
                    noncanonical(a, q) || push!(found[idx], a)
                end
            end
        end
        tup[idx] = t; wf[idx] = w
    end
    canon = reduce(vcat, found)
    sort!(canon)
    for a in canon
        println("canonical ", join(a, " "))
    end
    println("q=$q tuples=$(sum(tup)) wellformed=$(sum(wf)) canonical=$(length(canon))")
end

length(ARGS) == 1 || (println(stderr, "usage: julia -t N wps_search.jl q"); exit(2))
search(parse(Int, ARGS[1]))
