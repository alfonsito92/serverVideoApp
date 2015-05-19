/**
Copyright (C) 2015  Cristian Alfonso Prieto Sánchez

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
GNU General Public License for more details.

You should have getTransmitErrorCountd a copy of the GNU General Public License
along with this program. If not, see <http://www.gnu.org/licenses/>.
*/

package ugr.cristian.serverVideoApp;

/**
*@author Cristian Alfonso Prieto Sánchez
*/

import java.lang.System;
import java.util.concurrent.Semaphore;

import java.net.InetAddress;
import java.net.UnknownHostException;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.Iterator;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentMap;
import java.util.Map;
import java.util.HashMap;
import java.util.Set;
import java.util.HashSet;

import org.opendaylight.controller.sal.action.Action;
import org.opendaylight.controller.sal.action.Controller;
import org.opendaylight.controller.sal.action.Output;
import org.opendaylight.controller.sal.action.SetDlDst;
import org.opendaylight.controller.sal.action.SetDlSrc;
import org.opendaylight.controller.sal.action.SetNwDst;
import org.opendaylight.controller.sal.action.SetNwSrc;
import org.opendaylight.controller.sal.core.ConstructionException;
import org.opendaylight.controller.sal.core.Bandwidth;
import org.opendaylight.controller.sal.core.Node;
import org.opendaylight.controller.sal.core.Edge;
import org.opendaylight.controller.sal.core.Host;
import org.opendaylight.controller.sal.core.Latency;
import org.opendaylight.controller.sal.core.Property;
import org.opendaylight.controller.sal.core.Path;
import org.opendaylight.controller.sal.core.NodeConnector;
import org.opendaylight.controller.sal.flowprogrammer.Flow;
import org.opendaylight.controller.sal.flowprogrammer.IFlowProgrammerService;
import org.opendaylight.controller.sal.match.Match;
import org.opendaylight.controller.sal.match.MatchField;
import org.opendaylight.controller.sal.match.MatchType;
import org.opendaylight.controller.sal.packet.BitBufferHelper;
import org.opendaylight.controller.sal.packet.Ethernet;
import org.opendaylight.controller.sal.packet.IDataPacketService;
import org.opendaylight.controller.sal.packet.IListenDataPacket;
import org.opendaylight.controller.sal.packet.IPv4;
import org.opendaylight.controller.sal.packet.ICMP;
import org.opendaylight.controller.sal.packet.TCP;
import org.opendaylight.controller.sal.packet.UDP;
import org.opendaylight.controller.sal.packet.Packet;
import org.opendaylight.controller.sal.packet.PacketResult;
import org.opendaylight.controller.sal.packet.RawPacket;
import org.opendaylight.controller.sal.reader.FlowOnNode;
import org.opendaylight.controller.sal.reader.NodeConnectorStatistics;
import org.opendaylight.controller.sal.utils.IPProtocols;
import org.opendaylight.controller.sal.utils.Status;
import org.opendaylight.controller.switchmanager.ISwitchManager;
import org.opendaylight.controller.topologymanager.ITopologyManager;
import org.opendaylight.controller.statisticsmanager.IStatisticsManager;

import edu.uci.ics.jung.algorithms.shortestpath.DijkstraShortestPath;
import edu.uci.ics.jung.graph.Graph;
import edu.uci.ics.jung.graph.SparseMultigraph;
import edu.uci.ics.jung.graph.util.EdgeType;

import org.apache.commons.collections15.Transformer;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class ICMPRouting {

  private static final Logger log = LoggerFactory.getLogger(PacketHandler.class);

  private Map<Node, Set<Edge>> nodeEdges = new HashMap<Node, Set<Edge>>();

  private ConcurrentMap<Map<Node, Node>, List<Edge>> icmpPathMap = new ConcurrentHashMap<Map<Node, Node>, List<Edge>>();

  private Edge edgeMatrix[][];

  private Long latencyMatrix[][];
  private Long minLatency;
  private Long mediumLatencyMatrix[][];
  private Long minMediumLatency;

  private Long icmpCostMatrix[][];

  private Transformer<Edge, ? extends Number> icmpCostTransformer = null;

  private Graph<Node, Edge> g = new SparseMultigraph();
	private DijkstraShortestPath<Node, Edge> icmpShortestPath;

  private Map<Edge, Long> icmpEdgeCostMap = new HashMap<Edge, Long>();

  private ConcurrentMap<Edge, Map<String, ArrayList>> edgeStatistics = new ConcurrentHashMap<Edge, Map<String, ArrayList>>();
  private Map<String, Long> maxStatistics = new HashMap<String, Long>();

  /*********Statistics Constants**********/

  private final String transmitBytes = "Transmits Bytes";
  private final String receiveBytes = "Receive Bytes";
  private final String transmitDropBytes = "Transmit Drop Bytes";
  private final String receiveDropBytes = "Receive Drop Bytes";
  private final String transmitErrorBytes = "Transmit Error Bytes";
  private final String receiveErrorBytes = "Receive Error Bytes";
  private final String[] statisticsName = {transmitBytes, receiveBytes, transmitDropBytes,
  receiveDropBytes, transmitErrorBytes, receiveErrorBytes};
  /***************************************/
  /*************************************/
  private final Long defaultCost = 5L; //If we don't have any latency measure
  /**************************************/

  public boolean needUpdate = false;

  /**
	*Constructor for ICMPRouting class
	*@param nodes The nodeEdges map
	*@param edges The edgeMatrix
	*@param latencies The latencyMatrix
	*@param latency The min latency
	*@param medLatencies The mediumLatencyMatrix
	*@param medLatency The min mediumLatency value
	*@param statistics The edgeStatisticsMap
	*@param max The maximum statistics
	*@param grapho The topology Graph
	*/

  public ICMPRouting(Map<Node, Set<Edge>> nodes, Edge edges[][], Long latencies[][], Long latency, Long medLatencies[][], Long medLatency,
	ConcurrentMap<Edge, Map<String, ArrayList>> statistics, Map<String, Long> max, Graph<Node, Edge> grapho){

		this.nodeEdges = nodes;
		this.edgeMatrix = edges;
		this.latencyMatrix = latencies;
		this.minLatency = latency;
		this.mediumLatencyMatrix = medLatencies;
		this.minMediumLatency = medLatency;
		this.edgeStatistics = statistics;
		this.maxStatistics = max;

		this.g = grapho;

    this.icmpPathMap = new ConcurrentHashMap<Map<Node, Node>, List<Edge>>();

		buildICMPCostMatrix();
		buildICMPTransformerMap(this.icmpEdgeCostMap);

	}

  /**
  *This function try to assing a cost for each Edge attending the latency and
  *medium latency and other aspects like statistics
  */

  private void buildICMPCostMatrix(){
    int l = this.nodeEdges.size();
    int h = this.nodeEdges.size();
    this.icmpCostMatrix = new Long[l][h];
    this.icmpEdgeCostMap.clear();

    for(int i=0; i<l; i++){

      for(int j=0; j<h; j++){

        if(i==j){
          this.icmpCostMatrix[i][j]=0L;
        }
        else{
          if(this.edgeMatrix[i][j]==null){
            this.icmpCostMatrix[i][j]=null;
          }
          else{
            this.icmpCostMatrix[i][j] = icmpEvaluationLatencyCost(this.edgeMatrix[i][j]) +
            icmpEvaluationStatisticsCost(this.edgeMatrix[i][j])/10;
          }
        }
        icmpEdgeCostMap.put(this.edgeMatrix[i][j], this.icmpCostMatrix[i][j]);
      }
    }
  }

  /**
  *Function that is called when is necessary to build the transformer for Dijkstra
  *@param edgeCostMap2 The edgeCostMap which is necessary to call the constructor
  *of the transformer
  */

  private void buildICMPTransformerMap(final Map<Edge, Long> edgeCostMap2){

    icmpCostTransformer = new Transformer<Edge, Long>(){
      public Long transform(Edge e){

        return edgeCostMap2.get(e);
      }
    };

  }

  /**
  *This method provide the possibility to get a index for a nodeConnector
  *@param nodeConnector The nodeConnector.
  */

  private int getNodeConnectorIndex(NodeConnector nodeConnector){

    int index;
    Node node = nodeConnector.getNode();
    index = Integer.parseInt(node.getID().toString());
    return index-1;

  }

  /**
  *This function is called when is necessary evaluate the latencyMatrix for an edge
  *@param edge The edge
  *@return The Long value after the process
  */

  private Long icmpEvaluationLatencyCost(Edge edge){
    int i = getNodeConnectorIndex(edge.getTailNodeConnector());
    int j = getNodeConnectorIndex(edge.getHeadNodeConnector());

    Long ret1 = 0L;
    Long ret2 = 0L;

    Long cost;
    if(latencyMatrix!=null){
      Long temp = this.latencyMatrix[i][j];
      Long temp2 = this.mediumLatencyMatrix[i][j];

      if(temp == null){
        ret1=defaultCost;
      }
      else{
        ret1 = temp/minLatency;
      }

      if(temp2 == null){
        ret2=defaultCost;
      }
      else{
        ret2=temp2/minMediumLatency;
      }
    }
    else{
      ret1=defaultCost;
      ret2=defaultCost;
    }

    cost = ret1/2 + ret2;
    return cost;
  }

  /**
  *This function is called when is necessary evaluate the statisticsMap for an edge
  *@param edge The edge
  *@return The Long value after the process
  */

  private Long icmpEvaluationStatisticsCost(Edge edge){
    Long cost = 0L;
    Long temp1 = 0L;
    Long temp2 = 0L;

    ArrayList<Long> tempArray = new ArrayList<Long>();

    Map<String, ArrayList> tempStatistics = this.edgeStatistics.get(edge);
    for(int i=0; i<statisticsName.length; i++){
      tempArray = tempStatistics.get(statisticsName[i]);

      if(tempArray == null){

        tempArray=new ArrayList<Long>();
        tempArray.add(10L);
        tempArray.add(10L);

      }

      if(tempArray.get(0)!=0 && tempArray.get(1) !=0 ){
        Long tempMedium = (tempArray.get(0) + tempArray.get(1) )/ 2;

        Long tempMax = maxStatistics.get(statisticsName[i]);

        if(tempMax == null){
          tempMax = tempMedium;
        }


        if(tempMax/tempMedium > 9){
          cost += 1L;
        }
        else{
          cost += 10L - tempMax/tempMedium;
        }
      }
      else{
        cost += 1L;
      }
    }
    return cost/2;
  }

  /**
  *This function reordenate a Edge<List> to put in the correct order.
  *@param path The List<Edge>
  *@param srcNode The first Node
  *@param dstNode The last Node
  *@return The definitive List<Edge>
  */

  private List<Edge> reordenateList(List<Edge> path, Node srcNode, Node dstNode){
    boolean orden = true;
    boolean orientacion = true;

    List<Edge> result = new ArrayList();
    List<Edge> definitivePath = new ArrayList();

    if(path.get(0).getTailNodeConnector().getNode().equals(srcNode)){
      orden=true;
      orientacion=true;
    }
    else if(path.get(0).getHeadNodeConnector().getNode().equals(srcNode)){
      orden=true;
      orientacion=false;
    }
    else if(path.get(path.size()-1).getTailNodeConnector().getNode().equals(srcNode)){
      orden=false;
      orientacion=true;
    }
    else if(path.get(path.size()-1).getHeadNodeConnector().getNode().equals(srcNode)){
      orden=false;
      orientacion=false;
    }

    int i=0;
    int n1=0;
    int n2=0;

    if(!orden){
      i=path.size()-1;
    }
    int index;
    for(int j=0; j<path.size();j++){

      if(!orden){
        index=i-j;
      }
      else{
        index=j;
      }

      Edge tempEdge = path.get(index);

      if(!orientacion){
        n1=getNodeConnectorIndex(tempEdge.getHeadNodeConnector());
        n2=getNodeConnectorIndex(tempEdge.getTailNodeConnector());
      }else{
        n1=getNodeConnectorIndex(tempEdge.getTailNodeConnector());
        n2=getNodeConnectorIndex(tempEdge.getHeadNodeConnector());
      }
      result.add(this.edgeMatrix[n1][n2]);
    }

    ////////////////////////
    //Better reordenating
    ///////////////////////

    definitivePath.add(result.get(0));


    for(int j=1; j<result.size(); j++){

      Edge tempEdge2 = result.get(j);
      Edge tempEdge1 = result.get(j-1);

      Node tempNode1 = tempEdge1.getHeadNodeConnector().getNode();
      Node tempNode2 = tempEdge2.getTailNodeConnector().getNode();

      Node tempNodeAux = tempEdge2.getHeadNodeConnector().getNode();


      if(tempNode1.equals(tempNode2)){
        definitivePath.add(result.get(j));
      }else if(tempNode1.equals(tempNodeAux)){
        int aux1 = getNodeConnectorIndex(tempEdge2.getHeadNodeConnector());
        int aux2 = getNodeConnectorIndex(tempEdge2.getTailNodeConnector());

        definitivePath.add(this.edgeMatrix[aux1][aux2]);
      }
    }

    return definitivePath;

  }


  /******************************PUBLIC METHODS*****************************/

	/**
	*This fucntion is called when is necessary get the best path between two nodes
	*@param srcNode The srcNode
	*@param dstNode The dstNode
	*@return result The resultan path
	*/

	public List<Edge> getICMPShortestPath(Node srcNode, Node dstNode){

		List<Edge> tempPath;
    List<Edge> definitivePath;

		if(this.g == null || this.g.getEdgeCount() == 0){
			needUpdate = true;
		}

		Map<Node, Node> tempMap = new HashMap<Node, Node>();
		tempMap.put(srcNode, dstNode);

		if(this.icmpPathMap.containsKey(tempMap)){
			tempPath = this.icmpPathMap.get(tempMap);
		}else{
			this.icmpShortestPath = new DijkstraShortestPath<Node,Edge>(this.g, this.icmpCostTransformer);
			tempPath = icmpShortestPath.getPath(srcNode, dstNode);
			this.icmpPathMap.put(tempMap, tempPath);
		}

    boolean temp = tempPath.get(0).getTailNodeConnector().getNode().equals(srcNode);

    if(!temp){
      definitivePath = reordenateList(tempPath, srcNode, dstNode);
    }
    else{
      definitivePath = tempPath;
    }

		return definitivePath;

	}

  /**
  *This function del old ICMP flows when an Edge is down
  *@param edge The Edge which is down now
  *@param flowProgrammer The service which enable the posibility to del or install flows
  *@param statisticsManager The statistics manager to obtain the flows on a Node.
  */

  public void removeFlows(Edge edge, IFlowProgrammerService flowProgrammerService, IStatisticsManager statisticsManager){
    Set<Map<Node, Node>> tempMaps = icmpPathMap.keySet();

    if(tempMaps.isEmpty()){
      Set<Node> nodes = this.nodeEdges.keySet();

      for(Iterator it = nodes.iterator(); it.hasNext();){
        Node tempNode = (Node)it.next();

        List<FlowOnNode> flowsOnNode = new ArrayList();

        try{
          flowsOnNode = statisticsManager.getFlows(tempNode);
        }
        catch(RuntimeException bad){
          log.trace("No flows get, time to try in noCache flows");
          try{
            flowsOnNode = statisticsManager.getFlowsNoCache(tempNode);
          }
          catch(RuntimeException veryBad){
            log.trace("Impossible to obtain the flows");
          }
        }

        for(int j = 0; j<flowsOnNode.size(); j++){
          FlowOnNode tempFlowOnNode = flowsOnNode.get(j);
          Flow tempFlow = tempFlowOnNode.getFlow();

          if(tempFlow!=null){
            MatchField tempField = tempFlow.getMatch().getField(MatchType.NW_PROTO);
            MatchField tempField2 = new MatchField(MatchType.NW_PROTO, IPProtocols.ICMP.byteValue());

            if(tempField.equals(tempField2)){
              try{
                log.trace("Trying removing "+tempFlow+" on "+tempNode);
                flowProgrammerService.removeFlow(tempNode, tempFlow);
              }
              catch(RuntimeException e8){
                log.trace("Error removing flow");
              }
            }
          }
        }
      }
    }
    else{
      for(Iterator it = tempMaps.iterator(); it.hasNext();){
        Map<Node, Node> tempMap = (Map<Node, Node>)it.next();
        List<Edge> tempPath = icmpPathMap.get(tempMap);

        if(tempPath.contains(edge)){

          for(int i=0; i<tempPath.size(); i++){
            Edge tempEdge = tempPath.get(i);
            Node tempNode = tempEdge.getTailNodeConnector().getNode();

            List<FlowOnNode> flowsOnNode = new ArrayList();

            try{
              flowsOnNode = statisticsManager.getFlows(tempNode);
            }
            catch(RuntimeException bad){
              log.trace("No flows get, time to try in noCache flows");
              try{
                flowsOnNode = statisticsManager.getFlowsNoCache(tempNode);
              }
              catch(RuntimeException veryBad){
                log.trace("Impossible to obtain the flows");
              }
            }

            for(int j = 0; j<flowsOnNode.size(); j++){
              FlowOnNode tempFlowOnNode = flowsOnNode.get(j);
              Flow tempFlow = tempFlowOnNode.getFlow();

              if(tempFlow!=null){
                MatchField tempField = tempFlow.getMatch().getField(MatchType.NW_PROTO);
                MatchField tempField2 = new MatchField(MatchType.NW_PROTO, IPProtocols.ICMP.byteValue());

                if(tempField.equals(tempField2)){
                  try{
                    log.trace("Trying removing "+tempFlow+" on "+tempNode);
                    flowProgrammerService.removeFlow(tempNode, tempFlow);
                  }
                  catch(RuntimeException e8){
                    log.trace("Error removing flow");
                  }
                }
              }
            }
          }
          for(int i=0; i<tempPath.size(); i++){
            Edge tempEdge = tempPath.get(i);
            Node tempNode = tempEdge.getHeadNodeConnector().getNode();

            List<FlowOnNode> flowsOnNode = new ArrayList();

            try{
              flowsOnNode = statisticsManager.getFlows(tempNode);
            }
            catch(RuntimeException bad){
              log.trace("No flows get, time to try in noCache flows");
              try{
                flowsOnNode = statisticsManager.getFlowsNoCache(tempNode);
              }
              catch(RuntimeException veryBad){
                log.trace("Impossible to obtain the flows");
              }
            }

            for(int j = 0; j<flowsOnNode.size(); j++){
              FlowOnNode tempFlowOnNode = flowsOnNode.get(j);
              Flow tempFlow = tempFlowOnNode.getFlow();

              if(tempFlow!=null){
                MatchField tempField = tempFlow.getMatch().getField(MatchType.NW_PROTO);
                MatchField tempField2 = new MatchField(MatchType.NW_PROTO, IPProtocols.ICMP.byteValue());

                if(tempField.equals(tempField2)){
                  try{
                    log.trace("Trying removing "+tempFlow+" on "+tempNode);
                    flowProgrammerService.removeFlow(tempNode, tempFlow);
                  }
                  catch(RuntimeException e8){
                    log.trace("Error removing flow");
                  }
                }
              }
            }
          }
        }
      }
    }
  }


	/**
	*Function that is called when is necessary to update the icmpCostMartix
	*@param latencies The latencyMatrix
	*@param latency The min latency
	*@param medLatencies The mediumLatencyMatrix
	*@param medLatency The min mediumLatency value
	*@param statistics The edgeStatisticsMap
	*@param max The maximum statistics
	*/

	public void updateStandardCostMatrix(Long latencies[][], Long latency, Long medLatencies[][], Long medLatency,
	ConcurrentMap<Edge, Map<String, ArrayList>> statistics, Map<String, Long> max){

		this.latencyMatrix = latencies;
		this.minLatency = latency;
		this.mediumLatencyMatrix = medLatencies;
		this.minMediumLatency = medLatency;
		this.edgeStatistics = statistics;
		this.maxStatistics = max;

		buildICMPCostMatrix();

		buildICMPTransformerMap(this.icmpEdgeCostMap);

	}

	/**
	*Function that is called when is necessary to update the graph
	*@param grafo The new topologyGraph
	*/

	public void updateGraph(Graph grafo){
		this.g = grafo;
	}

}
