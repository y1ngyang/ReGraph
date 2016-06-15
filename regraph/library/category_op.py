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
                        if (A_s, A_t) not in h1.source_.edges():
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
                        if (A_s, A_t) not in h1.source_.edges() and (A_t, A_s) not in h1.source_.edges():
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


def pushout(hom):
    nodes = set([n for n in hom.target_.nodes() if n not in hom.mapping_.values()])

    node_attrs = {}
    for node in hom.source_.nodes():
        if node not in node_attrs.keys():
            node_attrs.update({node: {}})

        mapped_node = hom.mapping_[node]
        mapped_attrs = hom.target_.node[mapped_node].attrs_

        attrs = hom.source_.node[node].attrs_
        if mapped_attrs is not None and attrs is not None:
            for key, value in mapped_attrs.items():
                if key not in attrs.keys():
                    node_attrs[node].update({key: value})
                else:
                    node_attrs[node].update(
                        {key: set([el for el in value if el not in attrs[key]])})

    edges = dict()
    edge_attrs = {}

    for edge in hom.target_.edges():
        sources = keys_by_value(hom.mapping_, edge[0])
        targets = keys_by_value(hom.mapping_, edge[1])
        if len(sources) == 0 or len(targets) == 0:
            edges[(edge[0], edge[1])] = hom.target_.edge[edge[0]][edge[1]]
            continue
        for s in sources:
            for t in targets:
                if (s, t) not in hom.source_.edges():
                    edges[(edge[0], edge[1])] = hom.target_.edge[edge[0]][edge[1]]

    for edge in hom.source_.edges():
        if edge not in edge_attrs.keys():
            edge_attrs.update({edge: {}})

        mapped_edge = (hom.mapping_[edge[0]], hom.mapping_[edge[1]])
        mapped_attrs = hom.target_.edge[mapped_edge[0]][mapped_edge[1]]

        attrs = hom.source_.edge[edge[0]][edge[1]]

        for key, value in mapped_attrs.items():
            if key not in attrs.keys():
                edge_attrs[edge].update({key: value})
            else:
                edge_attrs[edge].update(
                    {key: set([el for el in value
                               if el not in attrs[key]])})
    return (nodes, edges, node_attrs, edge_attrs)
