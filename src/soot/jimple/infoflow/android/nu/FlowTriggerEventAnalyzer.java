package soot.jimple.infoflow.android.nu;

import java.io.IOException;
import java.text.MessageFormat;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.logging.Formatter;
import java.util.logging.Handler;
import java.util.logging.Level;
import java.util.logging.LogRecord;
import java.util.logging.Logger;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import com.sun.xml.internal.bind.v2.model.core.ID;

import soot.Immediate;
import soot.Local;
import soot.MethodOrMethodContext;
import soot.PointsToAnalysis;
import soot.PointsToSet;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.jimple.AnyNewExpr;
import soot.jimple.ArrayRef;
import soot.jimple.AssignStmt;
import soot.jimple.BinopExpr;
import soot.jimple.CastExpr;
import soot.jimple.ConcreteRef;
import soot.jimple.Constant;
import soot.jimple.DefinitionStmt;
import soot.jimple.Expr;
import soot.jimple.FieldRef;
import soot.jimple.IfStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InstanceOfExpr;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.NewArrayExpr;
import soot.jimple.NewExpr;
import soot.jimple.NewMultiArrayExpr;
import soot.jimple.NullConstant;
import soot.jimple.NumericConstant;
import soot.jimple.ParameterRef;
import soot.jimple.Ref;
import soot.jimple.Stmt;
import soot.jimple.StringConstant;
import soot.jimple.ThisRef;
import soot.jimple.UnopExpr;
import soot.jimple.infoflow.Infoflow;
import soot.jimple.infoflow.android.manifest.ProcessManifest;
import soot.jimple.infoflow.android.nu.FlowTriggerEventObject.EventID;
import soot.jimple.infoflow.android.nu.FlowTriggerEventObject.EventOriginObject;
import soot.jimple.infoflow.android.resources.ARSCFileParser;
import soot.jimple.infoflow.android.resources.ARSCFileParser.AbstractResource;
import soot.jimple.infoflow.android.resources.ARSCFileParser.ResConfig;
import soot.jimple.infoflow.android.resources.ARSCFileParser.ResPackage;
import soot.jimple.infoflow.android.resources.ARSCFileParser.ResType;
import soot.jimple.infoflow.results.InfoflowResults;
import soot.jimple.infoflow.results.ResultSinkInfo;
import soot.jimple.infoflow.results.ResultSourceInfo;
import soot.jimple.internal.ImmediateBox;
import soot.jimple.toolkits.callgraph.Edge;
import soot.shimple.ShimpleExpr;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.graph.Orderer;
import soot.toolkits.graph.PseudoTopologicalOrderer;
import soot.toolkits.graph.UnitGraph;
import soot.toolkits.scalar.LocalDefs;
import soot.util.queue.QueueReader;

public class FlowTriggerEventAnalyzer {
	public class MyFormatter extends Formatter {

	    /**
	     * @see java.util.logging.Formatter#format(java.util.logging.LogRecord)
	     */
	    @Override
	    public String format(final LogRecord record) {
	        return MessageFormat.format(record.getMessage(), record.getParameters());
	    }
	}
	
	private static final Logger log = Logger.getLogger("NUFlow");
	{
		//for(Handler h : log.getHandlers())
		//	h.setFormatter(new MyFormatter());
		log.setLevel(Level.ALL);
	}

	private List<ResPackage> resourcePackages;
	private InfoflowResults savedInfoFlow;
	private HashMap<String, FlowTriggerEventObject> flowTriggerEventObjectMap;
	private String  apkFileLocation;
	private String appPackageName;
	ProcessManifest processMan;
	ARSCFileParser resParser;
	private Map<Integer, List<String>> id2Text;
	
	public FlowTriggerEventAnalyzer( InfoflowResults savedInfoFlow, String apkFileLocation){
		this.flowTriggerEventObjectMap = new HashMap<String, FlowTriggerEventObject>();
		this.savedInfoFlow = savedInfoFlow;
		if(savedInfoFlow == null){
			System.err.println("error: infoflow is null!");
		}
		this.apkFileLocation =  apkFileLocation;
		this.processMan = null;
		try{
			processMan = new ProcessManifest(apkFileLocation);
		}
		catch(Exception e){
			log.severe("failed to init FlowTriggerEventAnalyzer: ProcessManifest");
			e.printStackTrace();
		}
		this.appPackageName = processMan.getPackageName();
		
		resParser = new ARSCFileParser();
		try {
			resParser.parse(apkFileLocation);
		} catch (Exception e) {
			log.severe("failed to init FlowTriggerEventAnalyzer: ARSCFileParser");
			e.printStackTrace();
		}
		this.resourcePackages = resParser.getPackages();	
		id2Text = null;
	}
	
	//DEBUG function, can be removed after testing.
	private Unit findConstructorInvokeStmt(Value objValue, Unit startingUnit, UnitGraph g){
		Set<Unit> visitedUnit = new HashSet<Unit>();
		Queue<Unit> q = new java.util.concurrent.LinkedBlockingQueue<Unit>();
		q.addAll(g.getSuccsOf(startingUnit));
		visitedUnit.add(startingUnit);
		
		while(!q.isEmpty()){
			Unit s = q.poll();
			visitedUnit.add(s);
			
			if(s instanceof InvokeStmt){
				InvokeStmt is = (InvokeStmt)s;
				InvokeExpr ie = is.getInvokeExpr();
				if(ie instanceof InstanceInvokeExpr){
					if(is.getInvokeExpr().getMethod().getName().equals("<init>") && 
							((InstanceInvokeExpr)ie).getBase().equivTo(objValue))
						return s;
				}
			}
			
			for(Unit child : g.getSuccsOf(s)){
				if (!visitedUnit.contains(child))
					q.add(child);
			}	
		}
		return null;
	}
	
	/* LIMITATION: 
	 *   1. Only works for intra-procedure analysis.
	 *   2. The View's layout has to be set by setContentView.
	 * */
	public void analyzeRegistrationCalls(){
		Map<String, String> view2Layout = new HashMap<String, String>();
		
		for (QueueReader<MethodOrMethodContext> rdr =
				Scene.v().getReachableMethods().listener(); rdr.hasNext(); ) {
			SootMethod m = rdr.next().method();
			if(!m.hasActiveBody())
				continue;
			String cls = m.getDeclaringClass().getName();
			UnitGraph g = new ExceptionalUnitGraph(m.getActiveBody());
		    LocalDefs localDefs = LocalDefs.Factory.newLocalDefs(g);
		    Orderer<Unit> orderer = new PseudoTopologicalOrderer<Unit>();
		    boolean changed = false;
		    //System.err.println("DEBUG=======================Start Method:"+m.getName()+" ==============");
		    for (Unit u : orderer.newList(g, false)) {
		    	Stmt s = (Stmt)u;
		    	//System.err.println("DEBUG: RunAnalysi Statement: "+s+" || "+s.getClass().getTypeName());
		    	if(s.containsInvokeExpr()){
		    		InvokeExpr expr = s.getInvokeExpr();
		    		SootMethod invokedM = expr.getMethod();
		    		
		    		//findViewById
		    		if(invokedM.getName().equals(FlowTriggerEventObject.onClickRegisterMethodName)){
		    			//setOnClickListener: find association of view and click event listener (source).
		    			//System.err.println("DEBUG setOnClickListener0: "+u);
		    			changed = true;
		    			Value arg = expr.getArg(0);
		    			if (! (arg instanceof Local) ) {
		    				System.err.println("error: setOnClickListener arg is not Local.");
		    				continue;   
		    			}
		    			Local larg = (Local)arg;
	    				List<Unit> defsOfUse = localDefs.getDefsOfAt(larg, u);
	    				if (defsOfUse.size() != 1){
	    					System.err.println("error: cannot find setOnClickListener arg defs");
	    					continue;
	    				}
	    				DefinitionStmt defStmt = (DefinitionStmt) defsOfUse.get(0);
	    				
	    				SootClass viewClass = invokedM.getDeclaringClass();
	    				String eventListenerClassName = defStmt.getRightOp().getType().toString();
	    				
	    				//V1.setOnClickListener(V2);
	    				List<ValueBox> values = u.getUseBoxes();
	    				if(values.size() != 3){
	    					System.err.println("error: the size of UseBoxes is not 2: "+values.size());
	    					continue;
	    				}
	    				Value obj = values.get(1).getValue();
	    				if(! (obj instanceof Local) ){
	    					System.err.println("error: setOnClickListener is not registered on a local variable.");
	    					continue;
	    				}
	    				
	    				Local lObj = (Local)obj;
	    				defsOfUse = localDefs.getDefsOfAt(lObj, u);
	    				if (defsOfUse.size() != 1){
	    					System.err.println("error: cannot find setOnClickListener source obj defs");
	    					continue;
	    				}
	    				defStmt = (DefinitionStmt) defsOfUse.get(0);
	    				//System.err.println("DEBUG setOnClickListener: "+lObj);
	    				
	    				Set<Unit> visitedStmts = new HashSet<Unit>();
	    				Queue<DefinitionStmt> stmtQueue = new LinkedBlockingQueue<DefinitionStmt>();
	    				visitedStmts.add(defStmt);
	    				stmtQueue.add(defStmt);
	    				//System.err.println("DEBUG start to find source of setOnClickListener: ");
	    				while(!stmtQueue.isEmpty()){
	    					defStmt = stmtQueue.poll();
	    					//System.err.println("  DEBUG find setOnClickListener Origin defOfView:"+defStmt);
	    					if(defStmt.getRightOp() instanceof ConcreteRef || 
	    							defStmt.getRightOp() instanceof CastExpr ||
	    							defStmt.getRightOp() instanceof Local){
	    						Value right = defStmt.getRightOp();
	    						if(defStmt.getRightOp() instanceof CastExpr ){
	    							CastExpr castExpr = (CastExpr)defStmt.getRightOp();
	    							right = castExpr.getOp();
	    						}
	    						
	    						for(Unit pred : g.getPredsOf(defStmt)){
	    							if(visitedStmts.contains(pred))
	    								continue;
	    							visitedStmts.add(pred);
	    							if(! (pred instanceof DefinitionStmt))
	    								continue;
	    							else {
	    								DefinitionStmt newDefStmt = (DefinitionStmt)pred;
	    								if(!newDefStmt.getLeftOp().equivTo(right))
	    									continue;
	    								stmtQueue.add(newDefStmt);
	    							}
	    						}
	    					}
	    					else if(defStmt.getRightOp() instanceof ThisRef){
	    						ThisRef tr = (ThisRef)(defStmt.getRightOp());
	    						String type = tr.getType().getEscapedName();
	    						//System.err.println("  THISREF: "+defStmt+" "+type+" "+cls);
	    						if (!flowTriggerEventObjectMap.containsKey(eventListenerClassName)){
    								//TODO: currently only works for onClick.
    								FlowTriggerEventObject eventObj = 
    										new FlowTriggerEventObject(EventID.onClick, eventListenerClassName);
    								flowTriggerEventObjectMap.put(eventListenerClassName, eventObj);
    								//TODO: the type is most generic one (e.g., View)/
    								eventObj.addTriggerEventSrcObject("-", type, cls, 0);
    							}
    							else
    								flowTriggerEventObjectMap.get(eventListenerClassName)
    									.addTriggerEventSrcObject("-", type, cls, 0);
	    					}
	    					else if(defStmt.getRightOp() instanceof ParameterRef){
	    						System.err.println("  GIVEUP. cannot find the origin of setOnClickListener: only do intra-procedure analysis.");
	    						break;
	    					}
	    					else if(defStmt.getRightOp() instanceof InvokeExpr){
	    						InvokeExpr ie = (InvokeExpr)(defStmt.getRightOp());
	    						if(ie.getMethod().getName().equals("findViewById")){
	    							String type = defStmt.getLeftOp().getType().toString();	
	    							int id = 0;
	    							try{
	    								id = Integer.valueOf(ie.getArg(0).toString());
	    							}
	    							catch(Exception e){
	    								System.err.println("error: findViewById's arg is not integer. "+ie);
	    							}
	    							//System.err.println("  SUCC: found source of setOnClickListener: "+ id+" T:"+type+" "+m.getDeclaringClass()+" "+
	    							//		" "+eventListenerClassName);
	    							
	    							if (!flowTriggerEventObjectMap.containsKey(eventListenerClassName)){
	    								//TODO: currently only works for onClick.
	    								FlowTriggerEventObject eventObj = 
	    										new FlowTriggerEventObject(EventID.onClick, eventListenerClassName);
	    								flowTriggerEventObjectMap.put(eventListenerClassName, eventObj);
	    								//TODO: the type is most generic one (e.g., View)/
	    								eventObj.addTriggerEventSrcObject("", type, cls, id);
	    							}
	    							else
	    								flowTriggerEventObjectMap.get(eventListenerClassName)
	    									.addTriggerEventSrcObject("", type, cls, id);
	    						}
	    						else{
	    							System.err.println("  GIVEUP. cannot find the origin of setOnClickListener: unknown function call:"+ defStmt);
	    						}
	    					}
	    					else {
	    						System.err.println("  GIVEUP. cannot find the origin of setOnClickListener: unknown right op: "+defStmt);
	    						break;
	    					}
	    				}
		    		} //setOnClickListener
		    		else if(invokedM.getName().equals("setContentView")){
		    			//System.err.println("DEBUG setContentView: "+u);
		    			changed = true;
		    			Value arg = expr.getArg(0);
		    			if(! (arg instanceof IntConstant) ){
		    				System.err.println("error: setContentView arg is not integer.");
		    				continue;
		    			}
		    			IntConstant ib = (IntConstant)arg;
		    			
		    			//System.err.println("DEBUG setContentView: "+arg);
		    			List<ValueBox> values = u.getUseBoxes();
		    			if(values.size() != 3){
		    				System.err.println("error: setContentView invoke has "+values.size()+" use boexs. Should be 3.");
		    				continue;
		    			}
		    			Value obj = values.get(1).getValue();
	    				if(! (obj instanceof Local) ){
	    					System.err.println("error: setContentView is not called on a local variable.");
	    					continue;
	    				}
	    				Local lObj = (Local)obj;
	    				List<Unit> defsOfUse = localDefs.getDefsOfAt(lObj, u);
	    				if (defsOfUse.size() != 1){
	    					System.err.println("error: cannot find setContentView source obj defs");
	    					continue;
	    				}
	    				
	    				DefinitionStmt defStmt = (DefinitionStmt) defsOfUse.get(0);
	    				String viewClsName = defStmt.getRightOp().getType().toString();
	    				int layoutID = ib.value;
	    				
		    			for(ARSCFileParser.ResPackage rp : resourcePackages){
    						for (ResType rt : rp.getDeclaredTypes()){
    							if(!rt.getTypeName().equals("layout"))
    								continue;
    							for (ResConfig rc : rt.getConfigurations())
    								for (AbstractResource res : rc.getResources()){
    									if(res.getResourceID() == layoutID){
    										view2Layout.put(viewClsName, res.getResourceName());
    										//System.out.println("VIEW2LAYOUT: "+viewClsName+" "+res.getResourceName());
    									}
    								}
    						}
    					}
		    		} //setContentView
		    		//TODO: there are other setting view functions. such as addView or inflate.
		    	}
		    	
		    }
		    //if(changed)
		    //	displayGraph(g, m.getName(), null, false );
		}
		
		LayoutFileParserForTextExtraction lfp = null;
		
		lfp = new LayoutFileParserForTextExtraction(this.appPackageName, resParser);
		lfp.parseLayoutFileForTextExtraction(apkFileLocation);	
		id2Text = lfp.getId2Texts();
		
		//update flowTriggerEventObject's text attributes
		for(String listenerClass : flowTriggerEventObjectMap.keySet()){
			FlowTriggerEventObject obj = flowTriggerEventObjectMap.get(listenerClass);
			System.out.println("DEBUG: EventListenerClass Name: "+listenerClass);
			for(EventOriginObject oo : obj.getEventOriginObjects()){
				//oo.setText(findResourceID());
				if(id2Text.containsKey(oo.getId()) ){
					List<String> tmp = id2Text.get(oo.getId());
					String texts = "";
					for(String s : tmp){
						if (texts.length() > 0)
							texts += "\n";
						texts += s.trim();
					}
					oo.setText(texts);
				}
				if(view2Layout.containsKey(oo.getDeclaringClass())){
					String layoutName = (String)view2Layout.get(oo.getDeclaringClass());
					if(lfp.getTextTreeMap().containsKey(layoutName)){
						oo.setDeclaringClsLayoutTextTree(lfp.getTextTreeMap().get(layoutName));
					}
				}
				System.out.println("DEBUG:  RS:"+oo.toString());
			}
			System.out.println();
		}
		
		for(ResultSinkInfo sink: savedInfoFlow.getResults().keySet()){
			Set<ResultSourceInfo> sources = savedInfoFlow.getResults().get(sink);
			for(ResultSourceInfo source : sources){
				System.out.println("SOURCE: "+source.getSource());
			}
		}
		
		//TODO:
		//We still need to go back from source to the DummyMain class
		//Then we can start to associate each source to texts
	}
	
	/* The type could be "id" or "string" */
	private int findResourceID(String name, String type){
		for(ARSCFileParser.ResPackage rp : resourcePackages){
			for (ResType rt : rp.getDeclaredTypes()){
				if(!rt.getTypeName().equals(type))
					continue;
				for (ResConfig rc : rt.getConfigurations())
					for (AbstractResource res : rc.getResources()){
						//System.err.println("DEBUG ID: "+res.getResourceName()+" => "+res.getResourceID());
						if (res.getResourceName().equalsIgnoreCase(name))
							return res.getResourceID();
					}
				}
		}
		return 0;
	}
	
	public InfoflowResults getSavedInfoFlow(){
		return this.savedInfoFlow;
	}
	public Map<String, FlowTriggerEventObject> getFlowTriggerEventObjectMap(){
		return this.flowTriggerEventObjectMap;
	}
	
	static public void displayGraph(UnitGraph g,String graphName, List<Unit> startingUnits, boolean reverse){
		if(startingUnits == null)
			startingUnits = g.getHeads();
		Queue<Pair<Unit, Integer>> queue = new java.util.concurrent.LinkedBlockingQueue<Pair<Unit, Integer>>();
		Set<Unit> visitedUnits = new HashSet<Unit>();
		System.err.println("DEBUG DisplayGraph: "+graphName);
		for(Unit su : startingUnits){
			if(!visitedUnits.contains(su)){
				queue.add(new Pair<Unit, Integer>(su, 1));
				visitedUnits.add(su);
			}
		}
		
		while(!queue.isEmpty()){
			Pair<Unit, Integer> item = queue.poll();
			String space = new String(new char[item.second*2]).replace('\0', ' ');
			System.err.println("  DEBUG G:"+space+item.first+" ");
			//if(item.second > 20)
			//	break;
			List<Unit> next = (reverse? g.getPredsOf(item.first) : g.getSuccsOf(item.first));
			for(Unit n : next){
				if(!visitedUnits.contains(n)){
					queue.add(new Pair<Unit, Integer>(n, item.second+1));
					visitedUnits.add(n);
				}
			}
		}
		System.err.println();
	}
}