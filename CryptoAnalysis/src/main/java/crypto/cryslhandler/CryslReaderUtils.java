package crypto.cryslhandler;

import crypto.rules.CrySLMethod;
import de.darmstadt.tu.crossing.crySL.*;
import de.darmstadt.tu.crossing.crySL.impl.ObjectDeclImpl;

import java.util.AbstractMap.SimpleEntry;
import java.util.ArrayList;
import java.util.List;
import java.util.Map.Entry;

public class CryslReaderUtils {

	protected static List<CrySLMethod> resolveAggregateToMethodeNames(final Event leaf) {
		if (leaf instanceof Aggregate) {
			return dealWithAggregate((Aggregate) leaf);
		} else {
			final ArrayList<CrySLMethod> statements = new ArrayList<>();
			CrySLMethod stringifyMethodSignature = stringifyMethodSignature(leaf);
			if (stringifyMethodSignature != null) {
				statements.add(stringifyMethodSignature);
			}
			return statements;
		}
	}
	protected static List<CrySLMethod> dealWithAggregate(final Aggregate ev) {
		final List<CrySLMethod> statements = new ArrayList<>();

		for (final Event lab : ev.getLab()) {
			if (lab instanceof Aggregate) {
				statements.addAll(dealWithAggregate((Aggregate) lab));
			} else {
				statements.add(stringifyMethodSignature(lab));
			}
		}
		return statements;
	}
	protected static CrySLMethod stringifyMethodSignature(final Event lab) {
		if (!(lab instanceof SuperType)) {
			return null;
		}
		final Method method = ((SuperType) lab).getMeth();
		
		final String qualifiedName;
		if (method.getMethName().getSimpleName() != null) {
			final String fqClassName = ((ObjectDeclImpl) method.getInvokedObject().eContainer()).getObjectType().getIdentifier();
			final String methodName = method.getMethName().getSimpleName();
			qualifiedName = String.format("%s.%s", fqClassName, methodName);
		} else {
			qualifiedName = method.getMethName().getQualifiedName();
		}

		final List<Entry<String, String>> pars = new ArrayList<>();
		final de.darmstadt.tu.crossing.crySL.Object returnValue = method.getLeftSide();
		Entry<String, String> returnObject = null;
		if (returnValue != null && returnValue.getName() != null) {
			final ObjectDecl v = ((ObjectDecl) returnValue.eContainer());
			returnObject = new SimpleEntry<>(returnValue.getName(), v.getObjectType().getQualifiedName() + ((v.getArray() != null) ? v.getArray() : ""));
		} else {
			returnObject = new SimpleEntry<>("_", "void");
		}
		final ParList parList = method.getParList();
		if (parList != null) {
			for (final Par par : parList.getParameters()) {
				String parValue = "_";
				if (par.getVal() != null && par.getVal().getName() != null) {
					final ObjectDecl objectDecl = (ObjectDecl) par.getVal().eContainer();
					parValue = par.getVal().getName();
					final String parType = objectDecl.getObjectType().getIdentifier() + ((objectDecl.getArray() != null) ? objectDecl.getArray() : "");
					pars.add(new SimpleEntry<>(parValue, parType));
				} else {
					pars.add(new SimpleEntry<>(parValue, "AnyType"));
				}
			}
		}
		return new CrySLMethod(qualifiedName, pars, new ArrayList<Boolean>(), returnObject);
	}
	
}

