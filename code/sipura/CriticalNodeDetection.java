package sipura;

import kotlin.Pair;
import sipura.alg.Connectivity;
import sipura.alg.Neighbors;
import sipura.generate.GraphIO;
import sipura.generate.GraphRelations;
import sipura.graphs.SimpleGraphUndo;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.*;
import java.util.function.Function;
import java.util.stream.Collectors;

public class CriticalNodeDetection {
    final Random r = new Random();
    SimpleGraphUndo<Integer> g;
    List<Integer> vulnerable;
    List<Integer> nonDeletable;
    List<List<Integer>> cComponents;
    Map<Integer, Set<Integer>> connectedComponentByNode;
    int MAX_ITR;
    List<List<Integer>> TABU;
    int k;  
    double x; 
    final String example = "data/exampleGraph.txt";
    final String bioDM = "data/bio-DM-LC.edges";
    final String g3 = "data/g3.txt";
    public Function<SimpleGraphUndo<Integer>, List<Integer>> startingFunc;
    public String localSearchFunc;
    double p;
    double startingGoodness;

    static List<Solution> solutionList = new ArrayList<>();
    static List<Solution> localSearchList = new ArrayList<>();
    static List<Long> runtimes = new ArrayList<>();

    boolean neighFlag = false;

    CriticalNodeDetection(String path, String commentPrefix, String vulnPrefix) {
        vulnerable = new ArrayList<>();
        g = new SimpleGraphUndo<>(GraphIO.INSTANCE.importSimpleGraphFromFile(path, vulnPrefix, (x) -> {
            String[] lines = x.split(" ");
            Integer first = Integer.parseInt(lines[0].trim()) - 1;
            Integer second = Integer.parseInt(lines[1].trim()) - 1;
            return new Pair<>(first, second);
        }));
        try {
            String lines = new String(Files.readAllBytes(Paths.get(path)));
            lines.lines().filter(x -> x.startsWith("!")).forEach(f -> {
                Integer first = Integer.parseInt(f.trim().substring(1));
                vulnerable.add(first);
            });
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
        cComponents = connectedComponents(g);
    }

    public static void main(String[] args) {
        if (args.length <= 2) {
            System.out.println("There needs to be a path, an integer k and a function name.");
            System.exit(0);
        }
        String path = args[0];
        CriticalNodeDetection cnd = new CriticalNodeDetection(path, "@", "!");
        cnd.p = Double.parseDouble(args[1]);
        cnd.startingFunc = cnd.functionMapping(args[2]);

        cnd.MAX_ITR = 2;

        cnd.localSearchFunc = switch (args[2]) {
            case "highdegree", "mis" -> "fillToKRandomNDV";
            case "vuln", "neigh" -> "fillToKHighDegreeNDV";
            case "random" -> "fillToKRandomNDV";
            default -> "fillToKRandomNDV";
        };
        cnd.reductionOne();
        List<Integer> critical;
        List<List<Integer>> cCopy = new ArrayList<>(cnd.cComponents);
        cnd.startingGoodness = cnd.graphAVulnerability(cCopy);

        for (int h = 0; h < 3; h++) {
            cnd.k = switch (h) {
                case 0 -> 1 + (int) ((cnd.p / 10.0) * cnd.g.getV().size());
                case 1 -> 1 + (int) ((cnd.p / 5.0) * cnd.g.getV().size());
                default -> 1 + (int) ((cnd.p / 2.0) * cnd.g.getV().size());
            };
            long duration = 0;
            System.out.println("\nRunning " + args[0] + " with p=" + args[1] + ", k=" + cnd.k + ", max_iter=" + cnd.MAX_ITR + ", N=" + cnd.g.getV().size() + ", func=" + args[2] + " and filling=" + cnd.localSearchFunc);
            for (int i = 0; i < cnd.MAX_ITR; i++) {
                long startTime = System.nanoTime();
                SimpleGraphUndo<Integer> iterationCopy = new SimpleGraphUndo<>(cnd.g);
                critical = cnd.cnpndv(iterationCopy, cnd.startingFunc, cnd.graphAVulnerability);
                for (Integer q : critical) {
                    iterationCopy.removeVertex(q);
                }
                double goodness = cnd.graphAVulnerability(cnd.connectedComponents(iterationCopy));
                solutionList.add(new Solution(critical, goodness));

                SimpleGraphUndo<Integer> searchCopy = new SimpleGraphUndo<>(cnd.g);
                List<Integer> improvedCritical = cnd.localSearchNDV(searchCopy, critical, cnd.graphAVulnerability, goodness);
                for (Integer t : improvedCritical) {
                    searchCopy.removeVertex(t);
                }
                double improvedGoodness = cnd.graphAVulnerability(cnd.connectedComponents(searchCopy));
                solutionList.add(new Solution(improvedCritical, improvedGoodness));
                long endTime = System.nanoTime();
                duration += (endTime - startTime);  
                runtimes.add((endTime - startTime));
            }

            double seconds = (duration / 1000000000.0) / cnd.MAX_ITR;
            DoubleSummaryStatistics stats = solutionList.stream().collect(Collectors.summarizingDouble(Solution::value));
            List<Double> medianList = solutionList.stream().mapToDouble(Solution::value).boxed().toList();

            double median;
            if (medianList.size() % 2 == 0) {
                median = (medianList.get(medianList.size() / 2) + medianList.get(medianList.size() / 2 - 1)) / 2;
            } else
                median = medianList.get(medianList.size() / 2);

            System.out.printf("Average runtime over " + cnd.MAX_ITR + " iterations is: %.2fs \n" +
                    "Starting goodness: %.2f \n" +
                    "Best goodness: %.2f \n" +
                    "Worst goodness: %.2f \n" +
                    "Average goodness: %.2f \n" +
                    "Median goodness: %.2f \n", seconds, cnd.startingGoodness, stats.getMin(), stats.getMax(), stats.getAverage(), median);

        }
    }

    public List<Integer> cnpv(SimpleGraphUndo<Integer> g, Function<SimpleGraphUndo<Integer>, List<Integer>> startingPopulation, Function<List<List<Integer>>, Double> goodness) {
        if (k >= vulnerable.size()) {
            return new ArrayList<>(vulnerable);
        }

        List<Integer> cut = startingPopulation.apply(g);
        List<Integer> critical = chooseTopK(cut);
        SimpleGraphUndo<Integer> local = removeAll(g, critical);

        while (k > critical.size()) {
            int diff = k - critical.size();
            List<Integer> fill = switch (localSearchFunc) {
                case "fillToKVulnerable" -> fillToKVulnerable(diff, local, critical);
                case "fillToKHighDegree" -> fillToKHighDegree(diff, local, critical);
                case "fillToKRandom" -> fillToKRandom(diff, local, critical);
                default -> fillToKRandom(diff, local, critical);
            };

            critical.addAll(new ArrayList<>(fill));
            for (Integer f : critical) {
                local.removeVertex(f);
            }

            cComponents = connectedComponents(local);
        }

        return critical;
    }

    List<Integer> fillToKHighDegree(int diff, SimpleGraphUndo<Integer> g, List<Integer> critical) {

        List<Integer> possibleVuln = new ArrayList<>();
        g.getV()
                .stream()
                .filter(x -> !critical.contains(x))
                .map(g::degreeOf)
                .sorted(Collections.reverseOrder())
                .limit(diff)
                .forEach(possibleVuln::add);

        if (possibleVuln.size() < diff) {
            possibleVuln.addAll(fillToKRandom(diff - possibleVuln.size(), g, critical));
            return possibleVuln;
        }

        return possibleVuln.subList(0, diff);
    }

    List<Integer> fillToKHighDegreeNDV(int diff, SimpleGraphUndo<Integer> g, List<Integer> critical) {

        List<Integer> possibleVuln = new ArrayList<>();
        g.getV()
                .stream()
                .filter(x -> !critical.contains(x) && !vulnerable.contains(x))
                .map(g::degreeOf)
                .sorted(Collections.reverseOrder())
                .limit(diff)
                .forEach(possibleVuln::add);

        if (possibleVuln.size() < diff) {
            possibleVuln.addAll(fillToKRandom(diff - possibleVuln.size(), g, critical));
            return possibleVuln;
        }

        return possibleVuln.subList(0, diff);
    }

    List<Integer> fillToKVulnerable(int diff, SimpleGraphUndo<Integer> g, List<Integer> critical) {

        List<Integer> possibleVuln = new ArrayList<>();
        vulnerable.stream()
                .filter(x -> !critical.contains(x) && vulnerable.contains(x))
                .unordered()
                .limit(diff)
                .forEach(possibleVuln::add);

        if (possibleVuln.size() < diff) {
            possibleVuln.addAll(fillToKVulnNeigh(diff - possibleVuln.size(), g, critical));
            return possibleVuln;
        }

        if (possibleVuln.size() > diff) {
            List<Integer> ret = new ArrayList<>();
            r.ints(0, possibleVuln.size())
                    .distinct()
                    .limit(diff)
                    .map(possibleVuln::get)
                    .forEach(ret::add);
            return ret;
        }

        return possibleVuln;
    }

    List<Integer> fillToKVulnNeigh(int diff, SimpleGraphUndo<Integer> g, List<Integer> critical) {
        List<Integer> possibleNeigh = new ArrayList<>();
        for (Integer t : vulnerable) {
            Set<Integer> neighs = new HashSet<>(g.neighbors(t));
            for (Integer q : neighs) {
                if (!critical.contains(q)) {
                    possibleNeigh.add(q);
                }
            }
        }

        if (possibleNeigh.size() < diff) {
            neighFlag = true;
            possibleNeigh.addAll(fillToKRandom(diff - possibleNeigh.size(), g, possibleNeigh));
            return possibleNeigh;
        }

        List<Integer> ret = new ArrayList<>();
        r.ints(0, possibleNeigh.size())
                .distinct()
                .limit(diff)
                .map(possibleNeigh::get)
                .forEach(ret::add);

        return ret;
    }

    List<Integer> fillToKVulnNeighNDV(int diff, SimpleGraphUndo<Integer> g, List<Integer> critical) {
        List<Integer> possibleNeigh = new ArrayList<>();
        for (Integer t : vulnerable) {
            Set<Integer> neighs = new HashSet<>(g.neighbors(t));
            for (Integer q : neighs) {
                if (!critical.contains(q) && vulnerable.contains(q)) {
                    possibleNeigh.add(q);
                }
            }
        }

        if (possibleNeigh.size() < diff) {
            possibleNeigh.addAll(fillToKRandom(diff - possibleNeigh.size(), g, possibleNeigh));
            return possibleNeigh;
        }

        List<Integer> ret = new ArrayList<>();
        r.ints(0, possibleNeigh.size())
                .distinct()
                .limit(diff)
                .map(possibleNeigh::get)
                .forEach(ret::add);

        return ret;
    }

    List<Integer> fillToKRandom(int diff, SimpleGraphUndo<Integer> g, List<Integer> critical) {
        List<Integer> possibleNeigh = new ArrayList<>();
        g.getV().stream()
                .filter(x -> !critical.contains(x))
                .unordered()
                .limit(diff)
                .forEach(possibleNeigh::add);

        if (possibleNeigh.size() < diff) {
            System.out.println("What the duck is happening ?!");
        }

        return possibleNeigh;
    }

    List<Integer> fillToKRandomNDV(int diff, SimpleGraphUndo<Integer> g, List<Integer> critical) {
        List<Integer> possibleNeigh = new ArrayList<>();
        g.getV().stream()
                .filter(x -> !critical.contains(x) && vulnerable.contains(x))
                .unordered()
                .limit(diff)
                .forEach(possibleNeigh::add);

        if (possibleNeigh.size() < diff) {
            System.out.println("What the duck is happening ?!");
        }

        return possibleNeigh;
    }

    private Integer exactEvaluation(SimpleGraphUndo<Integer> g, Function<List<List<Integer>>, Double> goodness, SimpleGraphUndo<Integer> local) {
        Map<Double, List<Integer>> current = new HashMap<>();
        local.getV()
                .stream()
                .map(x -> computingNodes(g, x, goodness))
                .forEach(min -> current.computeIfAbsent(min.value, y -> new ArrayList<>(min.node)).add(min.node));

        List<Integer> minNodes = current.get(Collections.min(current.keySet()));

        return minNodes.get(r.nextInt(minNodes.size()));
    }

    private List<Integer> chooseTopK(List<Integer> critical) {
        if (critical.size() <= k) {
            return critical;
        }

        List<Integer> topK = new ArrayList<>();
        r.ints(0, critical.size())
                .distinct()
                .limit(k)
                .map(critical::get)
                .forEach(topK::add);

        return topK;
    }



    public List<Integer> cnpndv(SimpleGraphUndo<Integer> g, Function<SimpleGraphUndo<Integer>, List<Integer>> startingPopulation, Function<List<List<Integer>>, Double> goodness) {
        List<Integer> cut = startingPopulation.apply(g);
        List<Integer> critical = chooseTopK(cut);

        SimpleGraphUndo<Integer> local = removeAll(g, critical);

        while (k > critical.size()) {
            Map<Double, List<Integer>> current = new HashMap<>();
            int diff = k - critical.size();
            List<Integer> fill = switch (localSearchFunc) {
                case "fillToKHighDegree" -> fillToKHighDegreeNDV(diff, local, critical);
                case "fillToKRandom" -> fillToKRandomNDV(diff, local, critical);
                default -> fillToKRandomNDV(diff, local, critical);
            };

            critical.addAll(new ArrayList<>(fill));
            for (Integer f : critical) {
                local.removeVertex(f);
            }
            cComponents = connectedComponents(local);
        }

        return critical;
    }

    public List<Integer> localSearch(SimpleGraphUndo<Integer> g, List<Integer> currentSolution, Function<List<List<Integer>>, Double> goodness, Double currentValue) {
        long startTime = System.currentTimeMillis();

        if (currentSolution.size() < k) {
            return currentSolution;
        }


        SimpleGraphUndo<Integer> localCopy = new SimpleGraphUndo<>(g);
        Double bestValue = currentValue;
        List<Integer> bestSolution = new ArrayList<>(currentSolution);

        for (int x = 0; x < MAX_ITR; x++) {
            if (System.currentTimeMillis() - startTime >= 60000) {
                return bestSolution;
            }

            List<Integer> localSolution = new ArrayList<>(bestSolution);
            List<Integer> newSolution = new ArrayList<>();

            for (int i = k; i > 0; i--) {
                Collections.shuffle(localSolution);
                Integer neigh;
                Integer swap = localSolution.remove(i - 1);
                List<Integer> neighbor = g.neighbors(swap).stream().toList();
                if (!neighbor.isEmpty()) {
                    neigh = neighbor.get(r.nextInt(neighbor.size()));
                } else {
                    neigh = swap;
                }

                newSolution.add(neigh);
            }

            for (Integer i : newSolution) {
                localCopy.removeVertex(i);
            }

            Double newValue = goodness.apply(connectedComponents(localCopy));
            if (newValue < bestValue) {
                localSearchList.add(new Solution(newSolution, newValue));
                bestSolution = new ArrayList<>(newSolution);
                bestValue = newValue;
            }

            localCopy.undo(k);
        }

        return bestSolution;
    }

    public List<Integer> localSearchNDV(SimpleGraphUndo<Integer> g, List<Integer> currentSolution, Function<List<List<Integer>>, Double> goodness, Double currentValue) {
        long startTime = System.currentTimeMillis();

        if (currentSolution.size() < k) {
            return currentSolution;
        }


        SimpleGraphUndo<Integer> localCopy = new SimpleGraphUndo<>(g);
        Double bestValue = currentValue;
        List<Integer> bestSolution = new ArrayList<>(currentSolution);

        for (int x = 0; x < MAX_ITR; x++) {
            if (System.currentTimeMillis() - startTime >= 60000) {
                return bestSolution;
            }

            List<Integer> localSolution = new ArrayList<>(bestSolution);
            List<Integer> newSolution = new ArrayList<>();

            for (int i = k; i > 0; i--) {
                Collections.shuffle(localSolution);
                Integer neigh;
                Integer swap = localSolution.remove(i - 1);
                List<Integer> neighbor = g.neighbors(swap).stream().filter(vulnerable::contains).toList();
                if (!neighbor.isEmpty()) {
                    neigh = neighbor.get(r.nextInt(neighbor.size()));
                } else {
                    neigh = swap;
                }
                newSolution.add(neigh);
            }

            for (Integer i : newSolution) {
                localCopy.removeVertex(i);
            }

            Double newValue = goodness.apply(connectedComponents(localCopy));
            if (newValue < bestValue) {
                localSearchList.add(new Solution(newSolution, newValue));
                bestSolution = new ArrayList<>(newSolution);
                bestValue = newValue;
            }

            localCopy.undo(k);
        }

        return bestSolution;
    }

    private LocalMin computingNodes(SimpleGraphUndo<Integer> g, Integer e, Function<List<List<Integer>>, Double> goodness) {
        List<List<Integer>> localChange = dynamicUpdateConnectedComponents(g, e);
        double objectiveValue = goodness.apply(localChange);
        return new LocalMin(e, objectiveValue);
    }

    record LocalMin(Integer node, double value) {
    }

    record Solution(List<Integer> nodes, double value) {
    }

    final Function<SimpleGraphUndo<Integer>, List<Integer>> highDegreeStart = g -> g.getV().stream().sorted(Comparator.comparingInt(g::degreeOf)).toList();

    final Function<SimpleGraphUndo<Integer>, List<Integer>> highDegreeNDVStart = g -> g.getV().stream().filter(vulnerable::contains).sorted(Comparator.comparingInt(g::degreeOf)).toList();

  
    final Function<SimpleGraphUndo<Integer>, List<Integer>> misStart = g -> {
        List<Integer> mis = new ArrayList<>();
        List<Integer> nodes = new ArrayList<>(g.getV());
        nodes.sort(Comparator.comparingInt(g::degreeOf));

        while (!nodes.isEmpty()) {
            Integer temp = nodes.remove(0);
            mis.add(temp);
            nodes.removeAll(g.neighbors(temp));
        }
        return mis;
    };

    final Function<SimpleGraphUndo<Integer>, List<Integer>> vulnStart = vulnerableGraph -> new ArrayList<>(vulnerable);

    final Function<SimpleGraphUndo<Integer>, List<Integer>> neighStart = g -> {
        List<Integer> output = new ArrayList<>();
        vulnerable.forEach(x -> output.addAll(Neighbors.INSTANCE.closedNeighbors(g, x)));
        return output;
    };

    final Function<SimpleGraphUndo<Integer>, List<Integer>> neighStartNDV = g -> {
        List<Integer> output = new ArrayList<>();
        vulnerable.forEach(x -> output.addAll(Neighbors.INSTANCE.closedNeighbors(g, x).stream().filter(vulnerable::contains).toList()));
        return output;
    };

    final Function<SimpleGraphUndo<Integer>, List<Integer>> randomStart = g -> {
        List<Integer> nodes = new ArrayList<>(g.getV());
        List<Integer> output = new ArrayList<>();
        r.ints(0, g.getV().size())
                .distinct()
                .limit(k)
                .map(nodes::get)
                .forEach(output::add);
        return output;
    };
    final Function<SimpleGraphUndo<Integer>, List<Integer>> randomNDVStart = g -> {
        List<Integer> nodes = new ArrayList<>(g.getV());
        nodes = nodes.stream().filter(vulnerable::contains).toList();
        List<Integer> output = new ArrayList<>();
        r.ints(0, nodes.size())
                .distinct()
                .limit(k)
                .map(nodes::get)
                .forEach(output::add);
        return output;
    };

    final Function<SimpleGraphUndo<Integer>, List<Integer>> empty = g -> new ArrayList<>();

    final Function<SimpleGraphUndo<Integer>, List<Integer>> cutVertices = g -> Connectivity.INSTANCE
            .cutVerticesAndBridgeEdges(g)
            .getFirst()
            .stream()
            .toList();


    Double pairwise(List<List<Integer>> connectedComponents) {
        return connectedComponents
                .stream()
                .mapToDouble(x -> (x.size() * (x.size() - 1.0)) / 2.0)
                .sum();
    }


    Function<List<List<Integer>>, Double> graphAVulnerability = g -> g.stream().mapToDouble(this::aVulnerability).sum();

    Double graphAVulnerability(List<List<Integer>> connectedComponents) {
        return connectedComponents
                .stream()
                .mapToDouble(this::aVulnerability)
                .sum() - connectedComponents.size();
    }

    long aVulnerability(List<Integer> component) {
        List<Integer> localCopy = new ArrayList<>(component);
        long c = localCopy.size();
        localCopy.retainAll(vulnerable);
        long d = localCopy.size();
        return bCoefficient(d, 2) + d * (c - d);
    }

    public List<List<Integer>> connectedComponents(SimpleGraphUndo<Integer> g) {
        connectedComponentByNode = Connectivity.INSTANCE.listAllConnectedComponents(g);
        List<List<Integer>> cC = new ArrayList<>();
        Set<Integer> visited = new HashSet<>();

        for (Integer v : g.getV()) {
            if (!visited.contains(v)) {
                Set<Integer> current = connectedComponentByNode.get(v);
                visited.addAll(current);
                cC.add(new ArrayList<>(current));
            }
        }
        return cC;
    }

    public List<List<Integer>> dynamicUpdateConnectedComponents(SimpleGraphUndo<Integer> g, Integer node) {
        SimpleGraphUndo<Integer> localCopy = new SimpleGraphUndo<>(g);
        List<List<Integer>> localComponents = new ArrayList<>(cComponents);
        List<List<Integer>> newComponents = new ArrayList<>();
        Set<Integer> neigh = new HashSet<>(localCopy.neighbors(node));
        List<List<Integer>> naughtyComponents = localComponents.stream()
                .filter(x -> x.contains(node))
                .toList();
        Set<Integer> visited = new HashSet<>();

        localComponents.removeAll(naughtyComponents);
        localCopy.removeVertex(node);

        for (Integer o : neigh) {
            if (!visited.contains(o)) {
                Set<Integer> temp = Connectivity.INSTANCE.getConnectedComponent(localCopy, o);
                visited.addAll(temp);
                newComponents.add(new ArrayList<>(temp));
            }
        }

        localComponents.addAll(newComponents);
        return localComponents;
    }

    public long bCoefficient(long n, long k) {
        if (k > n - k) {
            k = n - k;
        }
        long b = 1;
        for (long i = 1, m = n; i <= k; i++, m--) {
            b = b * m / i;
        }
        return b;
    }


    public boolean reductionTwo(int x, int k) {
        return x < k;
    }

    public boolean reductionTwoNDV(int x, int k) {
        Set<Integer> VMinusA = new HashSet<>(g.getV());
        VMinusA.retainAll(vulnerable);
        if (VMinusA.size() > x) {
            return true;
        } else {
            SimpleGraphUndo<Integer> reduction = new SimpleGraphUndo<>(GraphRelations.INSTANCE.inducedSubgraph(g, VMinusA));
            return graphAVulnerability(connectedComponents(reduction)) <= x;
        }
    }

    public boolean reductionTrivial(int k) {
        return vulnerable.size() <= k;
    }

    public boolean reductionFour(int k, int x) {
        final double MAGIC_NUMBER = Math.sqrt(2 * x);
        int reduction = k;
        double threshold = k + MAGIC_NUMBER;

        List<List<Integer>> buckets = new ArrayList<>();
        for (int i = 0; i < vulnerable.size(); i++) {
            buckets.add(new ArrayList<>());
        }
        buckets.add(new ArrayList<>());

        for (Integer s : g.getV()) {
            Set<Integer> copy = new HashSet<>(g.neighbors(s));
            copy.retainAll(vulnerable);
            if (!copy.isEmpty()) {
                buckets.get(copy.size()).add(s);
            }
        }

        int i = vulnerable.size();
        while (i > threshold) {
            List<Integer> entries = buckets.get(i);
            while (!entries.isEmpty()) {
                Integer v = entries.remove(0);
                if (vulnerable.contains(v)) {
                    Set<Integer> localCopy = g.neighbors(v);
                    for (Integer o : localCopy) {
                        Set<Integer> n = new HashSet<>(g.neighbors(o));
                        n.retainAll(vulnerable);
                        buckets.get(n.size()).remove(o);
                        if (n.size() - 1 > threshold) {
                            buckets.get(n.size() - 1).add(v);
                        }
                    }
                    g.removeVertex(v);
                    vulnerable.remove(v);
                }
            }
            reduction -= 1;
            threshold = reduction + MAGIC_NUMBER;
            i -= 1;
        }
        return !(k == reduction);
    }

    public void reductionOne() {
        List<List<Integer>> common = cComponents.stream().filter(x -> Collections.disjoint(x, vulnerable)).toList();
        for (List<Integer> component : common) {
            for (Integer i : component) {
                g.removeVertex(i);
            }
        }
    }

    public SimpleGraphUndo<Integer> removeAll(SimpleGraphUndo<Integer> g, List<Integer> vertices) {
        SimpleGraphUndo<Integer> localCopy = new SimpleGraphUndo<>(g);
        for (Integer i : vertices) {
            localCopy.removeVertex(i);
        }
        return localCopy;
    }

    public String bitprint(int u) {
        String s = "";
        for (int n = 0; u > 0; ++n, u >>= 1)
            if ((u & 1) > 0) s += n + " ";
        return s;
    }

    public int bitcount(int u) {
        int n;
        for (n = 0; u > 0; ++n) {
            u &= (u - 1);
        }
        return n;
    }

    public List<List<Integer>> comb(int c, int n) {
        LinkedList<String> s = new LinkedList<>();
        for (int u = 0; u < 1 << n; u++) {
            if (bitcount(u) == c) s.push(bitprint(u));
        }

        List<List<Integer>> temp = new ArrayList<>();
        for (String t : s) {
            List<Integer> curr = Arrays.stream(t.split(" ")).map(x -> Integer.parseInt(x) + 1).toList();
            temp.add(curr);
        }
        return temp;
    }

    public Function<SimpleGraphUndo<Integer>, List<Integer>> functionMapping(String str) {
        return switch (str) {
            case "highdegree" -> highDegreeNDVStart;
            case "mis" -> misStart;
            case "vuln" -> vulnStart;
            case "neigh" -> neighStartNDV;
            case "random" -> randomNDVStart;
            default -> highDegreeNDVStart;
        };
    }
}
