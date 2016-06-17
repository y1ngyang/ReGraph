from regraph.library.data_structures import (TypedGraph,
                                             TypedDiGraph,
                                             Homomorphism)
from regraph.library.primitives import (merge_attributes)
from regraph.library.utils import keys_by_value


def pullback(h1, h2):
    """ Given h1 : B -> D; h2 : C -> D returns A, rh1, rh2
        with rh1 : A -> B; rh2 : A -> C """
    if h1.target_ != h2.target_:
        raise ValueError(
            "Homomorphisms don't have the same codomain, can't do pullback"
        )
    if type(h1.target_) == TypedGraph:
        res_graph = TypedGraph()
    else:
        res_graph = TypedDiGraph()
    hom1 = {}
    hom2 = {}
    for n1 in h1.source_.nodes():
        for n2 in h2.source_.nodes():
            if not h1.mapping_[n1] in res_graph.nodes():
                if h1.mapping_[n1] == h2.mapping_[n2]:
                    res_graph.add_node(
                        h1.mapping_[n1],
                        h1.target_.node[h1.mapping_[n1]].type_,
                        merge_attributes(h1.source_.node[n1].attrs_,
                                         h2.source_.node[n2].attrs_,
                                         'intersection'))

                    hom1[h1.mapping_[n1]] = n1
                    hom2[h2.mapping_[n2]] = n2

    for n1 in res_graph.nodes():
        for n2 in res_graph.nodes():
            if res_graph.is_directed():
                if (hom1[n1], hom1[n2]) in h1.source_.edges():
                    if (hom2[n1], hom2[n2]) in h2.source_.edges():
                        res_graph.add_edge(n1, n2)
                        res_graph.set_edge(
                            n1,
                            n2,
                            merge_attributes(
                                h1.source_.get_edge(hom1[n1], hom1[n2]),
                                h2.source_.get_edge(hom2[n1], hom2[n2]),
                                'intersection'))
            else:
                if (hom1[n1], hom1[n2]) in h1.source_.edges() or (hom1[n2], hom1[n1]) in h1.source_.edges():
                    if (hom2[n1], hom2[n2]) in h2.source_.edges() or (hom2[n2], hom2[n1]) in h2.source_.edges():
                        res_graph.add_edge(n1, n2)
                        res_graph.set_edge(
                            n1,
                            n2,
                            merge_attributes(
                                h1.source_.get_edge(hom1[n1], hom1[n2]),
                                h2.source_.get_edge(hom2[n1], hom2[n2]),
                                'intersection'))

    res_h1 = Homomorphism(res_graph, h1.source_, hom1)
    res_h2 = Homomorphism(res_graph, h2.source_, hom2)

    return res_graph, res_h1, res_h2



def final_PBC(h1, h2):
    if h1.target_ != h2.source_:
        raise ValueError(
            "Codomain of homomorphism 1 and domain of homomorphism 2 " +
            "don't match, can't do pullback complement"
        )

    if not h2.is_monic():
        raise ValueError(
            "Second homomorphism is not monic, cannot find final pullback complement"
        )

    if type(h1.target_) == TypedGraph:
        res_graph = TypedGraph()
    else:
        res_graph = TypedDiGraph()

    hom1 = {}
    hom2 = {}

    for node in h2.target_.nodes():
        B_node = keys_by_value(h2.mapping_, node)
        if len(B_node) > 0:
            mapped_A_nodes = keys_by_value(h1.mapping_, B_node[0])
            print(mapped_A_nodes)
            for A_node in mapped_A_nodes:
                res_graph.add_node(
                    str(A_node) + "_" + str(node),
                    h2.target_.node[h2.mapping_[h1.mapping_[A_node]]].type_,
                    merge_attributes(
                        h1.source_.node[A_node].attrs_,
                        h2.target_.node[h2.mapping_[h1.mapping_[A_node]]].attrs_,
                        "intersection"
                    )
                )
                hom1[A_node] = str(A_node) + "_" + str(node)
                hom2[str(A_node) + "_" + str(node)] = h2.mapping_[h1.mapping_[A_node]]
        else:
            res_graph.add_node(
                str(node) + "_",
                h2.target_.node[node].type_,
                h2.target_.node[node].attrs_
            )
            hom2[str(node) + "_"] = node
    for s, t in h2.target_.edges():
        B_s = keys_by_value(h2.mapping_, s)
        B_t = keys_by_value(h2.mapping_, t)
        if len(B_s) > 0 and len(B_t) > 0:
            mapped_A_ss = keys_by_value(h1.mapping_, B_s[0])
            mapped_A_ts = keys_by_value(h1.mapping_, B_t[0])
            for A_s in mapped_A_ss:
                for A_t in mapped_A_ts:
                    if res_graph.is_directed():
                        if hom1[A_s] == hom1[A_t] and (A_s, A_t) not in h1.source_.edges():
                            res_graph.add_edge(
                                hom1[A_s],
                                hom1[A_t],
                                h2.target_.get_edge(
                                    h2.mapping_[h1.mapping_[A_s]],
                                    h2.mapping_[h1.mapping_[A_t]])
                            )
                        else:
                            res_graph.add_edge(
                                hom1[A_s],
                                hom1[A_t],
                                merge_attributes(
                                    h1.source_.get_edge(A_s, A_t),
                                    h2.target_.get_edge(
                                        h2.mapping_[h1.mapping_[A_s]],
                                        h2.mapping_[h1.mapping_[A_t]]),
                                    "intersection"
                                )
                            )
                    else:
                        if hom1[A_s] == hom1[A_t] and (A_s, A_t) not in h1.source_.edges() and (A_t, A_s) not in h1.source_.edges():
                            res_graph.add_edge(
                                hom1[A_s],
                                hom1[A_t],
                                h2.target_.get_edge(
                                    h2.mapping_[h1.mapping_[A_s]],
                                    h2.mapping_[h1.mapping_[A_t]])
                            )
                            pass
                        else:
                            res_graph.add_edge(
                                hom1[A_s],
                                hom1[A_t],
                                merge_attributes(
                                    h1.source_.get_edge(A_s, A_t),
                                    h2.target_.get_edge(
                                        h2.mapping_[h1.mapping_[A_s]],
                                        h2.mapping_[h1.mapping_[A_t]]),
                                    "intersection"
                                )
                            )
        else:
            if len(B_s) == 0:
                sources_to_add = [str(s) + "_"]
            else:
                mapped_A_ss = keys_by_value(h1.mapping_, B_s[0])
                sources_to_add = [hom1[A_s] for A_s in mapped_A_ss]
            if len(B_t) == 0:
                targets_to_add = [str(t) + "_"]
            else:
                mapped_A_ts = keys_by_value(h1.mapping_, B_t[0])
                targets_to_add = [hom1[A_t] for A_t in mapped_A_ts]
            for new_s in sources_to_add:
                for new_t in targets_to_add:
                    res_graph.add_edge(
                        new_s,
                        new_t,
                        h2.target_.edge[s][t])
    res_h1 = Homomorphism(h1.source_, res_graph, hom1)
    res_h2 = Homomorphism(res_graph, h2.target_, hom2)

    return (res_graph, res_h1, res_h2)


def pushout(h1, h2):
    if h1.source_ != h2.source_:
        raise ValueError(
            "Domain of homomorphism 1 and domain of homomorphism 2 " +
            "don't match, can't do pushout"
        )

    hom1 = {}
    hom2 = {}

    if type(h1.target_) == TypedGraph:
        res_graph = TypedGraph()
    else:
        res_graph = TypedDiGraph()

    for node in h1.source_.nodes():
        res_graph.add_node(
            str(h1.mapping_[node]) + "_" + str(h2.mapping_[node]),
            h1.source_.node[node].type_,
            merge_attributes(
                h1.target_.node[h1.mapping_[node]].attrs_,
                h2.target_.node[h2.mapping_[node]].attrs_,
                "union"
            )
        )
        hom1[h1.mapping_[node]] =\
            str(h1.mapping_[node]) + "_" + str(h2.mapping_[node])
        hom2[h2.mapping_[node]] =\
            str(h1.mapping_[node]) + "_" + str(h2.mapping_[node])

    for s, t in h1.source_.edges():
        res_graph.add_edge(
            str(h1.mapping_[s]) + "_" + str(h2.mapping_[s]),
            str(h1.mapping_[t]) + "_" + str(h2.mapping_[t]),
            merge_attributes(
                h1.target_.get_edge(h1.mapping_[s], h1.mapping_[t]),
                h2.target_.get_edge(h2.mapping_[s], h2.mapping_[t]),
                "union"
            )
        )

    for node in h1.target_.nodes():
        if node not in h1.mapping_.values():
            res_graph.add_node(
                str(node) + "_",
                h1.target_.node[node].type_,
                h1.target_.node[node].attrs_
            )
            hom1[node] = str(node) + "_"

    for node in h2.target_.nodes():
        if node not in h2.mapping_.values():
            res_graph.add_node(
                str(node) + "_",
                h2.target_.node[node].type_,
                h2.target_.node[node].attrs_
            )
            hom2[node] = str(node) + "_"

    for s, t in h1.target_.edges():
        if s not in h1.mapping_.values() or t not in h1.mapping_.values():
            res_graph.add_edge(
                hom1[s],
                hom1[t],
                h1.target_.get_edge(s, t)
            )
        if res_graph.is_directed():
            if (hom1[s], hom1[t]) not in res_graph.edges():
                res_graph.add_edge(
                    hom1[s],
                    hom1[t],
                    h1.target_.get_edge(s, t)
                )
        else:
            if (hom1[s], hom1[t]) not in res_graph.edges() and (hom1[t], hom1[s]) not in res_graph.edges():
                res_graph.add_edge(
                    hom1[s],
                    hom1[t],
                    h1.target_.get_edge(s, t)
                )

    for s, t in h2.target_.edges():
        if s not in h2.mapping_.values() or t not in h2.mapping_.values():
            res_graph.add_edge(
                hom2[s],
                hom2[t],
                h2.target_.get_edge(s, t)
            )
        if res_graph.is_directed():
            if (hom2[s], hom2[t]) not in res_graph.edges():
                res_graph.add_edge(
                    hom2[s],
                    hom2[t],
                    h2.target_.get_edge(s, t)
                )
        else:
            if (hom2[s], hom2[t]) not in res_graph.edges() and (hom2[t], hom2[s]) not in res_graph.edges():
                res_graph.add_edge(
                    hom2[s],
                    hom2[t],
                    h2.target_.get_edge(s, t)
                )

    res_h1 = Homomorphism(h1.target_, res_graph, hom1)
    res_h2 = Homomorphism(h2.target_, res_graph, hom2)

    return (res_graph, res_h1, res_h2)
