
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.PriorityQueue;
import java.util.Random;
import java.util.TreeMap;

/**
 * 
 * @author TWODOG
 * 本文思路：
 * 1.最短路径用Dijkstra：邻接表+优先队列实现快速求解
 * 2.计算所有业务都跑最短路径下的带宽超出边，并计算每个业务代价，去掉拥堵边，计算代价差，从小到大排序，依次调度业务。
 * 3.用若干种方法去探索较优调度顺序，本文实现了4种，但还是交换法比较好一点
 * 4.根据探索结果逐步缩小搜索区域，因为前面换路代价高的业务，可以基本不用动，如果若干步长之后不能找到一个比当前解好的解，就缩搜索范围。直到60秒结束
 *
 */
public class Main {
	/**
	 * 全局变量
	 */
	static final int SUMMISSION = 1000;// 边数
	static final int SUMVEX = 500;// 顶点数
	static final int SUMEDGE = 1910;// 无向图总边数
	static final double alpha = 0.6; // 归一化的边权权重
	static final double beta = 0.4;// 带宽占有率权重

	public static void twoDarrayPrint(int a[][]) {
		for (int i = 0; i < a.length; i++) {
			for (int j = 0; j < a[i].length; j++) {
				System.out.print("  " + a[i][j]);
			}
			System.out.println();
		}
	}

	/**
	 * 【method】寻找一维数组的最大值
	 * 
	 * @param a
	 * @return
	 */
	public static int findMaxValue(int[] a) {
		int temp = Integer.MIN_VALUE;
		for (int i = 0; i < a.length; i++) {
			if (a[i] > temp) {
				temp = a[i];
			}
		}
		return temp;
	}

	public static double findMaxValue(double[] a) {
		double temp = Double.MIN_VALUE;
		for (int i = 0; i < a.length; i++) {
			if (a[i] > temp) {
				temp = a[i];
			}
		}
		return temp;
	}

	/**
	 * 【method】寻找一维数组的最小值
	 * 
	 * @param a
	 * @return
	 */
	public static int findMinValue(int[] a) {
		int temp = Integer.MAX_VALUE;
		for (int i = 0; i < a.length; i++) {
			if (a[i] < temp) {
				temp = a[i];
			}
		}
		return temp;
	}

	public static double findMinValue(double[] a) {
		double temp = Double.MIN_VALUE;
		for (int i = 0; i < a.length; i++) {
			if (a[i] < temp) {
				temp = a[i];
			}
		}
		return temp;
	}

	/**
	 * method:归一化权重
	 * 
	 * @param initW
	 * @return
	 */
	public static double[] updateW(int initW[], int Max, int Min) {
		double[] initWCopy = new double[initW.length];
		for (int i = 0; i < initW.length; i++) {
			initWCopy[i] = (double) (initW[i] - Min) / (Max - Min);
		}
		return initWCopy;
	}

	public static double[] updateW(double initW[], double Max, double Min) {
		double[] initWCopy = new double[initW.length];
		for (int i = 0; i < initW.length; i++) {
			initWCopy[i] = (initW[i] - Min) / (Max - Min);
		}
		return initWCopy;
	}

	/**
	 * [method]:邻接表+最小堆实现Dijkstra 权重为 INT
	 * 
	 * @param s
	 * @param e
	 * @param U
	 * @param V
	 * @param W
	 * @param first
	 * @param next
	 * @return
	 */

	// 【PriorityQueue Object】
	static class distanceTo {
		int des;
		int distance;

		distanceTo(int des, int distance) {
			this.des = des;
			this.distance = distance;
		}
	}

	public static LinkedList<Integer> findNearestPath(int s, int e, int U[], int V[], int W[], int[] first,
			int[] next) { // 源点i到其他点的最短路
		LinkedList<Integer> pathcopy = new LinkedList<>();
		int n = first.length;// 结点个数
		PriorityQueue<distanceTo> updatingDistance = new PriorityQueue<>(new Comparator<distanceTo>() {
			@Override
			public int compare(distanceTo o1, distanceTo o2) {
				return o1.distance - o2.distance;
			}
		});
		int[] distance = new int[n];// 到每个节点的距离
		for (int i = 0; i < n; ++i) {
			if (i == s)
				continue;
			distance[i] = Integer.MAX_VALUE;
		}
		int[] path = new int[n];// 每个点都存在上一步的最短路径节点
		for (int i = 0; i < path.length; i++) {
			path[i] = -1;// 初始化path的点
		}

		int i = first[s];
		if (i == -1) {
			pathcopy.addFirst(s);
			return pathcopy;
		}
		// 如果每边就返回全0 path数组！
		while (i != -1) { // 遍历s为源点的所有边
			distance[V[i]] = W[i];
			updatingDistance.offer(new distanceTo(V[i], W[i]));
			i = next[i];
		}
		for (i = 0; i < n; i++) { // 因为邻接表不会存不能直达的点
			if (distance[i] == Integer.MAX_VALUE)
				updatingDistance.offer(new distanceTo(i, distance[i]));
		}
		for (i = 0; !updatingDistance.isEmpty(); ++i) { // 循环到优先队列为空
			int t = first[updatingDistance.poll().des]; // 当前到点源点距离最短
			while (t != -1) {
				if (distance[V[t]] > distance[U[t]] + W[t]) {
					distance[V[t]] = distance[U[t]] + W[t];
					updatingDistance.offer(new distanceTo(V[t], distance[V[t]]));// 不需要删掉被覆盖的，因为他们会被排在后面
					path[V[t]] = U[t];
				}
				t = next[t];
			}
		}
		// 以起始节点到终止节点的路径输出
		int flagpath = e;// 标记位置,将结束节点赋给标记
		pathcopy.addFirst(e);
		while (flagpath != -1) {
			if (path[flagpath] != -1) {
				pathcopy.addFirst(path[flagpath]);
			}
			flagpath = path[flagpath];
		}
		pathcopy.addFirst(s);
		return pathcopy;
	}

	// 设置最短路径权值为double构造
	static class distanceDoubleTo {
		int des;
		double distance1;

		distanceDoubleTo(int des, double distance) {
			this.des = des;
			this.distance1 = distance;
		}
	}

	/**
	 * [method]:邻接表+最小堆实现Dijkstra 权重为 Double
	 * 
	 * @param s
	 * @param e
	 * @param U
	 * @param V
	 * @param W
	 * @param first
	 * @param next
	 * @return
	 */

	public static LinkedList<Integer> findNearestPath(int s, int e, int U[], int V[], double W[], int[] first,
			int[] next) { // 源点i到其他点的最短路
		LinkedList<Integer> pathcopy = new LinkedList<>();
		int n = first.length;// 结点个数
		PriorityQueue<distanceDoubleTo> updatingDistance1 = new PriorityQueue<>(new Comparator<distanceDoubleTo>() {
			@Override
			public int compare(distanceDoubleTo oD1, distanceDoubleTo oD2) {
				return (int) (oD1.distance1 - oD2.distance1);
			}
		});
		double[] distance = new double[n];// 到每个节点的距离
		for (int i = 0; i < n; ++i) {
			if (i == s)
				continue;
			distance[i] = Integer.MAX_VALUE;
		}
		int[] path = new int[n];// 每个点都存在上一步的最短路径节点
		for (int i = 0; i < path.length; i++) {
			path[i] = -1;// 初始化path的点
		}

		int i = first[s];
		if (i == -1) {
			pathcopy.addFirst(s);
			return pathcopy;
		}
		// 如果每边就返回全0 path数组！
		while (i != -1) { // 遍历s为源点的所有边
			distance[V[i]] = W[i];
			updatingDistance1.offer(new distanceDoubleTo(V[i], W[i]));
			i = next[i];
		}
		for (i = 0; i < n; i++) { // 因为邻接表不会存不能直达的点
			if (distance[i] == Integer.MAX_VALUE)
				updatingDistance1.offer(new distanceDoubleTo(i, distance[i]));
		}
		for (i = 0; !updatingDistance1.isEmpty(); ++i) { // 循环到优先队列为空
			int t = first[updatingDistance1.poll().des]; // 当前到点源点距离最短
			while (t != -1) {
				if (distance[V[t]] > distance[U[t]] + W[t]) {
					distance[V[t]] = distance[U[t]] + W[t];
					updatingDistance1.offer(new distanceDoubleTo(V[t], distance[V[t]]));// 不需要删掉被覆盖的，因为他们会被排在后面
					path[V[t]] = U[t];
				}
				t = next[t];
			}
		}

		// 以起始节点到终止节点的路径输出
		int flagpath = e;// 标记位置,将结束节点赋给标记
		pathcopy.addFirst(e);
		while (flagpath != -1) {
			if (path[flagpath] != -1) {
				pathcopy.addFirst(path[flagpath]);
			}
			flagpath = path[flagpath];
		}
		pathcopy.addFirst(s);

		return pathcopy;
	}

	public static int[][] gridTopo = new int[956][];// 存放原始拓扑信息
	public static int[][] request = new int[4001][];// 存放所有业务需求信息

	/**
	 * [method]:读取实验数据
	 * 
	 * @throws IOException
	 */
	public static void readTxt() throws IOException {
		String s;
		int i;
		// 1.read gridtopo

		BufferedReader in = new BufferedReader(new InputStreamReader(System.in));
		s = in.readLine();
		i = 0;
		for (i = 0; i < 956; i++) {
			String[] temp = s.split("\\ ");
			gridTopo[i] = new int[temp.length];
			for (int kk = 0; kk < temp.length; kk++) {
				gridTopo[i][kk] = Integer.parseInt(temp[kk]);
			}
			s = in.readLine();
		}
		// 2.read request
		i = 0;
		for (i = 0; i < 4001; i++) {
			String[] temp = s.split("\\ ");
			request[i] = new int[temp.length];
			for (int kk = 0; kk < temp.length; kk++) {
				request[i][kk] = Integer.parseInt(temp[kk]);
			}
			s = in.readLine();
		}
	}

	/**
	 * 【方法】一维数组从大到小排序并返回索引
	 */
	static class ValueComparator implements Comparator<Integer> {

		Map<Integer, Integer> base;

		public ValueComparator(Map<Integer, Integer> base) {
			this.base = base;
		}

		// Note: this comparator imposes orderings that are inconsistent with equals.
		// base.get(a) <= base.get(b)从小到大，base.get(a) >= base.get(b)从大到小排序
		public int compare(Integer a, Integer b) {
			if (base.get(a) >= base.get(b)) {
				return -1;
			} else {
				return 1;
			} // returning 0 would merge keys
		}
	}

	/**
	 * 按照后n业务的质量排序输出索引
	 * 
	 * @param n
	 * @param bestRandomOrder
	 * @param tempRandomOrder
	 * @param overLoadEdge
	 * @param sumBW1S
	 * @param u
	 * @param v
	 * @param w
	 * @param first
	 * @param next
	 * @param weightArray
	 * @param maxXLimitBWArray
	 * @param mission
	 * @return
	 */
	public static List<Integer> gnsOrderByM(int n, List<Integer> bestRandomOrder, List<Integer> tempRandomOrder, int mission[][]) {
		
		// -------------------后n个按照质量排序
		Map<Integer, Integer> relativepCostLastN = new HashMap<>();// 用map保存用质量，用于按代价从大到小排序输出索引
		for (int i = n; i < SUMMISSION; i++) {
			int missionIndex = bestRandomOrder.get(i);
			int M=mission[missionIndex][0];
			relativepCostLastN.put(missionIndex,M);
		}
		List<Integer> listLastN = new LinkedList<>();
		// 通过对质量从大到小更新顺序表
		ValueComparator bvc12 = new ValueComparator(relativepCostLastN);
		TreeMap<Integer, Integer> sorted_map = new TreeMap<Integer, Integer>(bvc12);
		sorted_map.putAll(relativepCostLastN);
		for (Integer missionkey : sorted_map.keySet()) {
			listLastN.add(missionkey);

		}
		for (int i = 0; i < SUMMISSION; i++) {
			if (i < n) {
				tempRandomOrder.add(bestRandomOrder.get(i));
			}

		}
		tempRandomOrder.addAll(listLastN);
		return tempRandomOrder;
	}

	/**
	 * 把当前最优序列根据与最短路径的代价从大到小进行排列
	 */

	/**
	 * 【按与无约束下的最短路径的代价差值从大到小排序】 按照代价大小去排序，但是只排n以后的顺序
	 * 
	 * @param bestRandomOrder
	 * @param tempRandomOrder
	 * @param sumBW1S
	 * @param u
	 * @param v
	 * @param w
	 * @param first
	 * @param next
	 * @param weightArray
	 * @param maxXLimitBWArray
	 * @param mission
	 * @return
	 */
	public static List<Integer> gnsOrder(int n, List<Integer> bestRandomOrder, List<Integer> tempRandomOrder,
			double[][] overLoadEdge, int[] sumBW1S, int[] u, int[] v, int w[], int[] first, int[] next,
			int[][] weightArray, int[][] maxXLimitBWArray, int mission[][]) {

		// -----------------------------根据与最短路径之间的消耗代价差的大小估计调度的大概顺序------------------------------------------

		// ------------------------初始化--------------------------------------------------------------------------------------

		int icopy;// 存放根据顺序得到的调度索引
		int[] sumXMissionCost = new int[SUMMISSION];// 初始化所有所有业务的代价
		int[][] sumXBWTemp = new int[SUMVEX][SUMVEX];// 初始化所有道路的带宽消耗量
		double[] wTemp = new double[SUMEDGE];// 初始化临时权重的值，视为安全权重
		Map<Integer, Integer> relativepCost = new HashMap<>();// 用map保存用与最短路径下的相对代价，用于按代价从大到小排序输出索引
		double BWOccupanceRate;// 带宽占用率

		// ------------------开始任务调度-------------------
		for (int i = 0; i < SUMMISSION; i++) {
			icopy = bestRandomOrder.get(i);// 按照调度顺序走

			// ------------------初始化安全权重为原来的权重---------------------
			for (int init = 0; init < SUMEDGE; init++) {
				wTemp[init] = w[init];
			}

			for (int j = 0; j < SUMEDGE; j++) {
				BWOccupanceRate = (1.0 * sumXBWTemp[u[j]][v[j]] + 1.0 * mission[icopy][0])
						/ (0.8 * maxXLimitBWArray[u[j]][v[j]]);
				if (sumXBWTemp[u[j]][v[j]] + mission[icopy][0] > maxXLimitBWArray[u[j]][v[j]] * 0.8) {// 选择此路会超过带宽就令其权重最大绕过此路
					wTemp[j] = Double.MAX_VALUE / 3;// 设置最大权重表示此路不通
				}
				if (overLoadEdge[u[j]][v[j]] != 0) {
					wTemp[j] = Double.MAX_VALUE / 3;// 设置最大权重表示此路不通
				}

			}
			LinkedList<Integer> path1 = findNearestPath(mission[icopy][1], mission[icopy][2], u, v, wTemp, first, next);// 求最短路径
			// 计算所有业务的总成本
			for (int j1 = 0; j1 < path1.size() - 1; j1++) {
				int s = path1.get(j1);
				int e = path1.get(j1 + 1);
				sumXBWTemp[s][e] += mission[icopy][0];// 计算每个边的带宽总量
				sumXMissionCost[icopy] += weightArray[s][e] * mission[icopy][0];
			}
			relativepCost.put(icopy, sumXMissionCost[icopy] - sumBW1S[icopy]);// 每个不跑最短路消耗的相对代价保存起来，比较
		}

		// -------------------后n个按照代价排序
		Map<Integer, Integer> relativepCostLastN = new HashMap<>();// 用map保存用与最短路径下的相对代价，用于按代价从大到小排序输出索引
		for (int i = n; i < SUMMISSION; i++) {
			int missionIndex = bestRandomOrder.get(i);
			relativepCostLastN.put(missionIndex, relativepCost.get(missionIndex));
		}

		List<Integer> listLastN = new LinkedList<>();
		// 通过对不走最短路径的损失从大到小更新顺序表
		ValueComparator bvc12 = new ValueComparator(relativepCostLastN);
		TreeMap<Integer, Integer> sorted_map = new TreeMap<Integer, Integer>(bvc12);
		sorted_map.putAll(relativepCostLastN);
		for (Integer missionkey : sorted_map.keySet()) {
			listLastN.add(missionkey);
		}
		for (int i = 0; i < SUMMISSION; i++) {
			if (i < n) {
				tempRandomOrder.add(bestRandomOrder.get(i));
			}
		}
		tempRandomOrder.addAll(listLastN);
		return tempRandomOrder;

	}

	/**
	 * 逆序操作【探索调度顺序方法】
	 * 
	 * @param bestRandomOrder
	 * @param tempRandomOrder
	 */

	public static void gnsInvertedSequence(int n, List<Integer> bestRandomOrder, List<Integer> tempRandomOrder) {
		if (n > 998) {
			n = 950;
		}
		for (int i = 0; i < bestRandomOrder.size(); i++) {
			tempRandomOrder.add(bestRandomOrder.get(i));
		}
		Random random = new Random();
		int ran1 = 0, ran2 = 0;
		while (ran1 > ran2 || (ran1 == ran2) || Math.abs(ran1 - ran2) == 1 || ran1 < n || ran2 < n) {
			ran1 = random.nextInt(65535) % SUMMISSION;
			ran2 = random.nextInt(65535) % SUMMISSION;
		}

		List<Integer> l1 = new LinkedList<>();
		List<Integer> l2 = new LinkedList<>();
		List<Integer> l3 = new LinkedList<>();
		List<Integer> l4 = new LinkedList<>();
		for (int i = 0; i < ran1; i++) {
			l1.add(tempRandomOrder.get(i));
		}
		for (int i = ran2; i < tempRandomOrder.size(); i++) {
			l2.add(tempRandomOrder.get(i));
		}
		for (int i = ran1; i < ran2; i++) {
			l3.add(tempRandomOrder.get(i));
		}
		Collections.reverse(l3);

		l4.addAll(l1);
		l4.addAll(l3);
		l4.addAll(l2);

		tempRandomOrder = l4;

	}

	/**
	 * 随机一组数 [method: ]Generate neighbor solution
	 * 
	 * @param bestRandomOrder
	 * @param tempRandomOrder 前n个保持不动，后面随机
	 * @return
	 */

	public static void gnsRandom(int n, List<Integer> bestRandomOrder, List<Integer> tempRandomOrder) {
		if (n > 998) {
			n = 900;
		}
		for (int i = 0; i < bestRandomOrder.size(); i++) {
			tempRandomOrder.add(bestRandomOrder.get(i));
		}
		List<Integer> l1 = new LinkedList<>();
		for (int i = n; i < SUMMISSION; i++) {
			l1.add(bestRandomOrder.get(i));
		}
		Collections.shuffle(l1);
		for (int i = 0; i < n; i++) {
			tempRandomOrder.add(bestRandomOrder.get(i));
		}
		tempRandomOrder.addAll(l1);
	}

	/**
	 * 【三变换】调度顺序的三变换法，任选两点插入其他点后面 做法：选取ran1，ran2之间的数字，插入ran3的后面
	 * 
	 * @param randomOrder
	 * @return
	 */
	public static void gns3(int n, List<Integer> bestRandomOrder, List<Integer> tempRandomOrder) {
		if (n > 998) {
			n = 900;
		}
		for (int i = 0; i < bestRandomOrder.size(); i++) {
			tempRandomOrder.add(bestRandomOrder.get(i));
		}
		Random random = new Random();
		int ran1 = 0, ran2 = 0, ran3 = 0;

		while (((ran1 == ran2) || (ran1 == ran3) || (ran2 == ran3) || (Math.abs(ran1 - ran2) == 1)) || ran1 < n
				|| ran2 < n || ran3 < n) {
			// while (((ran1 == ran2) || (ran1 == ran3)|| (ran2 == ran3) ||
			// (Math.abs(ran1-ran2)==1))) {
			ran1 = random.nextInt(65535) % SUMMISSION;
			ran2 = random.nextInt(65535) % SUMMISSION;
			ran3 = random.nextInt(65535) % SUMMISSION;
		}

		int temp1 = ran1;
		int temp2 = ran2;
		int temp3 = ran3;
		// 确保 ran1<ran2<ran3
		if (ran1 < ran2 && ran2 < ran3) {

		} else if (ran1 < ran3 && ran3 < ran2) {
			ran2 = temp3;
			ran3 = temp2;
		} else if (ran2 < ran1 && ran1 < ran3) {
			ran1 = temp2;
			ran2 = temp1;
		} else if (ran2 < ran3 && ran3 < ran1) {
			ran1 = temp2;
			ran2 = temp3;
			ran3 = temp1;
		} else if (ran3 < ran1 && ran1 < ran2) {
			ran1 = temp3;
			ran2 = temp1;
			ran3 = temp2;
		} else if (ran3 < ran2 && ran2 < ran1) {
			ran1 = temp3;
			ran3 = temp1;
		}
		for (int j = 0; j < ran2 - ran1 + 1; j++) {
			tempRandomOrder.add(ran3 + 1, tempRandomOrder.get(ran1));// 在最后一个数后循环插入值
			tempRandomOrder.remove(ran1);
		}

	}

	/**
	 * 交换法调整调度顺序
	 * 
	 * @param Best_random_list
	 * @param temp_random_list
	 */
	public static void gns2(int n, List<Integer> best_random_list, List<Integer> temp_random_list) {
		Random random = new Random();
		if (n > 998) {
			n = 900;
		}
		int i;
		int ran1, ran2;
		int best_random_listSize = best_random_list.size();
		for (i = 0; i < best_random_listSize; i++) {
			temp_random_list.add(best_random_list.get(i));
		}

		ran1 = random.nextInt(65535) % SUMMISSION;
		ran2 = random.nextInt(65535) % SUMMISSION;
		while (ran1 == ran2 || ran1 < n || ran2 < n) {
			// while (ran1 == ran2) {
			ran1 = random.nextInt(65535) % SUMMISSION;
			ran2 = random.nextInt(65535) % SUMMISSION;
		}
		int temp1 = temp_random_list.get(ran1);
		int temp2 = temp_random_list.get(ran2);
		temp_random_list.set(ran1, temp2);
		temp_random_list.set(ran2, temp1);
	}

/**
 * 主函数
 * @param args
 * @throws IOException
 */
	public static void main(String[] args) throws IOException {
		long startTime = System.currentTimeMillis();// 计时开始
		int[][] maxXLimitBWArray = new int[SUMVEX][SUMVEX];// 存储两节点之间的信息，[0]最大带宽
		int[][] weightArray = new int[SUMVEX][SUMVEX];// 画邻接矩阵的地图，可以知道两节点之间的权重

		// 1.输入
		readTxt();
		int mission[][] = new int[SUMMISSION][3];// [0]（带宽）质量，[1]起 [2]始节点
		Integer[] vex = new Integer[SUMVEX];
		for (int i = 0; i < vex.length; i++) {
			vex[i] = i;
		}

		// 邻接表画地图
		int u[] = new int[SUMEDGE];// 某边的道路起点
		int v[] = new int[SUMEDGE];// 某边的道路终点
		int w[] = new int[SUMEDGE];// 某边的道路权重
		int first[] = new int[SUMVEX];
		int next[] = new int[SUMEDGE];
		int indexTwoToZero = 0;// 双向图变无向图索引
		for (int i = 1; i < gridTopo.length; i++) {
			u[indexTwoToZero] = gridTopo[i][0];
			v[indexTwoToZero] = gridTopo[i][1];
			w[indexTwoToZero] = gridTopo[i][3];

			indexTwoToZero++;
			u[indexTwoToZero] = gridTopo[i][1];
			v[indexTwoToZero] = gridTopo[i][0];
			w[indexTwoToZero] = gridTopo[i][3];
			indexTwoToZero++;

			maxXLimitBWArray[gridTopo[i][0]][gridTopo[i][1]] = gridTopo[i][2];// 两节点的最大带宽
			maxXLimitBWArray[gridTopo[i][1]][gridTopo[i][0]] = gridTopo[i][2];// 两节点的最大带宽

		}

		// 邻接表初始化节点边信息
		for (int i = 0; i < first.length; i++) {
			first[i] = -1;
		}
		for (int i = 0; i < next.length; i++) {
			next[i] = first[u[i]];
			first[u[i]] = i;
		}

		// 画邻接矩阵地图
		for (int i = 1; i < gridTopo.length; i++) {
			weightArray[gridTopo[i][0]][gridTopo[i][1]] = gridTopo[i][3];
			weightArray[gridTopo[i][1]][gridTopo[i][0]] = gridTopo[i][3];
		}
		for (int i = 0; i < weightArray.length; i++) {
			for (int j = 0; j < weightArray.length; j++) {
				if (i == j) {
					weightArray[i][j] = 0;
				} else if (weightArray[i][j] == 0) {
					weightArray[i][j] = -1;
				}
			}
		}
		// twoDarrayPrint(map);
		// 业务信息
		for (int i = 1; i < request.length; i = i + 4) {
			mission[request[i][0]][0] = request[i][1];
			mission[request[i][0]][1] = request[i + 1][0];
			mission[request[i][0]][2] = request[i + 1][request[i + 1].length - 1];
		}

		int AllMissionSumCost = 0;// 每次规划的所有业务的总成本

		// 【【【【【【【【【【【【【【 【计算前期一个比较优秀的调度顺序】】】】】】】】】】】】】】】】】】】】】】】】】】】】】
		Map<Integer, Integer> relativepCost = new HashMap<>();// 用map保存用于排序输出索引
		int[] sumBW1S = new int[SUMMISSION];// [消耗代价]第1次求无约束条件下的所有路径的总成本保存到一维数组(sum Bandwidth First ShortestPath )
		int[] sumBW2S = new int[SUMMISSION];// [消耗代价]第2次求无约束条件下的所有路径的总成本保存到二维数组(sum Bandwidth First ShortestPath )
		double[][] overLoadDdge = new double[SUMVEX][SUMVEX];// 过载则标记过载总量。
		int[][] sumXBWArrayFS = new int[SUMVEX][SUMVEX];// 此模块的带宽总量，无约束条件下
		for (int i = 0; i < SUMMISSION; i++) {
			LinkedList<Integer> path1 = findNearestPath(mission[i][1], mission[i][2], u, v, w, first, next);// 最短路径求出来了
			// 计算所有业务的总成本
			for (int j = 0; j < path1.size() - 1; j++) {
				int s = path1.get(j);// 道路起点
				int e = path1.get(j + 1);// 道路终点
				sumXBWArrayFS[s][e] += mission[i][0];// 计算每个边的带宽总量
				sumBW1S[i] += weightArray[s][e] * mission[i][0];// 计算每个业务的最短路径的总成本
			}

		}

		// 计算带宽过载的边，标记为过载量
		for (int i = 0; i < v.length; i++) {
			if (sumXBWArrayFS[u[i]][v[i]] > maxXLimitBWArray[u[i]][v[i]] * 0.8) {
				overLoadDdge[u[i]][v[i]] = sumXBWArrayFS[u[i]][v[i]] - 0.8 * maxXLimitBWArray[u[i]][v[i]];
				// rate[u[i]][v[i]]=(double)sumXBWArrayFS[u[i]][v[i]]/(double)(maxXLimitBWArray[u[i]][v[i]]);
			}
		}
		double wCopyAFS[] = new double[SUMEDGE];
		for (int i = 0; i < wCopyAFS.length; i++) {
			if (overLoadDdge[u[i]][v[i]] != 0) {
				wCopyAFS[i] = Double.MAX_VALUE / 5;// 过载则全部不让通行
			} else {
				wCopyAFS[i] = w[i];
			}
		}

		// 第二次计算
		for (int i = 0; i < SUMMISSION; i++) {
			LinkedList<Integer> path1 = findNearestPath(mission[i][1], mission[i][2], u, v, wCopyAFS, first, next);// 最短路径求出来了
			// 计算所有业务的总成本
			for (int j = 0; j < path1.size() - 1; j++) {
				int s = path1.get(j);
				int e = path1.get(j + 1);
				// sumXBWArrayFS[s][e]+=mission[i][0];//计算每个边的带宽总量
				sumBW2S[i] += weightArray[s][e] * mission[i][0];// 计算每个业务的最短路径的总成本

			}
			relativepCost.put(i, sumBW2S[i] - sumBW1S[i]);// 每个不跑最短路消耗的代价保存起来，比较
		}
		// -------------------把相对代价排序结果归一化-----------------------------+
		double norRelaCost[] = new double[mission.length];
		for (int i = 0; i < mission.length; i++) {
			norRelaCost[i] = relativepCost.get(i);
		}
		// double norRelaCostFinal[] = updateW(norRelaCost, findMaxValue(norRelaCost),
		// findMinValue(norRelaCost));

		// -------------------把相对代价排序结果归一化-------进行概率网络预测----------------------+
		// 按相对消耗成本排序
		ValueComparator bvc = new ValueComparator(relativepCost);
		TreeMap<Integer, Integer> sorted_map1 = new TreeMap<Integer, Integer>(bvc);
		sorted_map1.putAll(relativepCost);
		int missionIndex[] = new int[mission.length];
		int missionindex1 = 0;
		for (Integer missionkey : sorted_map1.keySet()) {
			missionIndex[missionindex1++] = missionkey;
		}

		Map<Integer, LinkedList<Integer>> allMissionRoute_map = new HashMap<>();// 用map存储所有路径
		int allMissionCostcopy = Integer.MAX_VALUE; // 初始化成本临时最高,使得第一次提前求出的解一定可以保存下来。
		List<Integer> bestRand_list = new LinkedList<>();// 最优调度顺序

		// 初始序列 初始序列也可以设置一个相对比较优的解

		for (int i = 0; i < missionIndex.length; i++) {
			bestRand_list.add(missionIndex[i]);// 把按不走最短路径的代价消耗排序的较优值付给最佳随机解
		}

		/**
		 * 开始迭代参数
		 */
		int internalLoop = 500000;
		double wMax = (double) findMaxValue(w);
		int dValue = 0;// 好解与坏解之间的差值
		int stepLength = 65;// 随着迭代次数增加，n越来越往后
		int n = 100;// 从范围0开始
		int flag = 1;// 累计未找到较优解的次数
		int count=15;//每10次未找到就缩小搜索区域

		for (int iRand = 0; iRand < internalLoop; iRand++) {
			if (dValue > 0 && flag % count == 0) {
				n += stepLength;
			}
			double wSafe[] = new double[w.length];// 安全权重使得业务不超带宽

			// -------------------------------初始化参数----------------------------------
			AllMissionSumCost = 0;// 初始化所有道路总代价
			List<Integer> tempRand_list = new LinkedList<>();// 初始化临时调度顺序，为了创建最优解的邻居而不改变最优解
			int[][] sumXBW = new int[SUMVEX][SUMVEX];// 初始化两顶点之间的消耗带宽总量;每次循环都初始化为0
			double BWOccuRate;

			// ----【创建邻居】----------1.创建邻居的时候，不能改变 bestRand_list 的值
	
			if (iRand == 0) {
				tempRand_list = bestRand_list;// 用于使用第一次传进来的较优解
			}
		else if(Math.random()<0.2) {
				gns3(n, bestRand_list, tempRand_list);
			}
			else {
				gns2(n, bestRand_list, tempRand_list);
			}
		
			for (int i = 0; i < SUMMISSION; i++) {
				int icopy = tempRand_list.get(i); // 实际调度业务索引

				// --------------------------每次遍历新的业务都更新权重一次----------------------------
				for (int j = 0; j <SUMEDGE; j++) {
					wSafe[j] = w[j] / wMax;// ((double)w[j]-wMin)/(wMax-wMin);//归一化
				}
				// -----------------------------根据带宽占用更新道路安全权重--------------------------------
				for (int j = 0; j <SUMEDGE; j++) {
					BWOccuRate = (mission[icopy][0] + sumXBW[u[j]][v[j]]) / (0.8 * maxXLimitBWArray[u[j]][v[j]]);// 两点之间的带宽占用率													
					if (sumXBW[u[j]][v[j]] + mission[icopy][0] > maxXLimitBWArray[u[j]][v[j]] * 0.8) {
						wSafe[j] = Double.MAX_VALUE / 3;// 设置最大权重表示此路不通
					}

					// -----------------------【将带宽利用率高的路段的权重也设置大一点，但是仅仅在前面没安排的时候设置】----------------------
					else {
						if (BWOccuRate > 0.5) {
							wSafe[j] = alpha * wSafe[j] + beta * BWOccuRate;
							
						}
					}
					
				}

				List<Integer> path = new LinkedList<>();

				path = findNearestPath(mission[icopy][1], mission[icopy][2], u, v, wSafe, first, next);// 根据安全权重求最短路径
				

				// ---------------------计算所有业务的总成本--------------（此总成本为全局变量）--------------------------------
				for (int j = 0; j < path.size() - 1; j++) {
					int s = path.get(j);
					int e = path.get(j + 1);
					sumXBW[s][e] += mission[icopy][0]; // 更新X边带宽消耗量
					AllMissionSumCost += weightArray[s][e] * mission[icopy][0];// 更新本次所有调度总成本
				}
			}
			

			dValue = AllMissionSumCost - allMissionCostcopy;// 与上一次的差有多少，差比较大的话就用二交换，比较小的话就用三交换：大动干戈
			if (dValue < 0) {
				allMissionCostcopy = AllMissionSumCost;
							bestRand_list = tempRand_list;// 把临时值赋给best值，这样改变temp的值，则best的值也改变
			} else {
				flag += 1;//标记为了缩小搜索区域
			}

			if (System.currentTimeMillis() - startTime > 58000) {
				break; // 到达时间退出！
			}
		}

//【【【【【【【【【【【【【【【【【【【【【【以下为取得迭代最优参数最后一次求路径】】】】】】】】】】】】】】】】】】】】】】】】】】】】】】】】】】】】
		// 以下计算也可以省略，可以在上一步骤保存路径

		int[][] sumXBW = new int[SUMVEX][SUMVEX]; // 初始化每条道路的占用带宽总量为0
		double[] wCopy = new double[w.length];
		int allMissionCostFinal = 0;// 初始化最后一次计算的总成本为0
		int icopy;

		for (int i = 0; i < SUMMISSION; i++) {

			// --------------------------------------迭代得到的最优的调度顺序放到这里-----------------------------------------
			icopy = bestRand_list.get(i);

			// 每次遍历新的任务都更新权重一次
			for (int j = 0; j < w.length; j++) {
				wCopy[j] = w[j] / wMax;// 归一化
			}

			for (int j = 0; j < u.length; j++) {
				double BWOccuRate = (mission[icopy][0] + sumXBW[u[j]][v[j]]) / (0.8 * maxXLimitBWArray[u[j]][v[j]]);// 两点之间的带宽占用率（Bandwidth
																													// occupancy
																													// Rate）
				if (sumXBW[u[j]][v[j]] + mission[icopy][0] > maxXLimitBWArray[u[j]][v[j]] * 0.8) {// 选择此路会超过带宽就令其权重最大绕过此路
					wCopy[j] = Double.MAX_VALUE / 3;// 设置最大权重表示此路不通

				}

				// -----------------------【将带宽利用率高的路段的权重也设置大一点，但是仅仅在前面没安排的时候设置】----------------------
				else {
					if (BWOccuRate > 0.55) {
						wCopy[j] = alpha * wCopy[j] + beta * BWOccuRate;
					}
				}
			}

			LinkedList<Integer> pathX = findNearestPath(mission[icopy][1], mission[icopy][2], u, v, wCopy, first, next);// 最短路径求出来了

			// 计算所有业务的总成本
			for (int j = 0; j < pathX.size() - 1; j++) {
				int s = pathX.get(j);
				int e = pathX.get(j + 1);
				sumXBW[s][e] = sumXBW[s][e] + mission[icopy][0];
				allMissionCostFinal += weightArray[s][e] * mission[icopy][0];// 每次加入边上的成本
			}
			allMissionRoute_map.put(icopy, pathX);// 用map存储

		}

		// -------------------------------------输出信息-------------------------------------------------------------------------
		System.out.println(allMissionCostFinal);
		for (int i = 0; i < SUMMISSION; i++) {
			System.out.print(i + " " + mission[i][0]);
			System.out.println();
			for (int j = 0; j < allMissionRoute_map.get(i).size(); j++) {
				System.out.print(allMissionRoute_map.get(i).get(j) + " ");
			}
			System.out.println();
		}
	
	}
}
