package it.unisa.uniclass.testing.benchmark.jmh.utenti.mocks;

import java.util.*;

public class MockCoordinatoreDAO implements CoordinatoreRemote {

    private final Map<String, Coordinatore> byEmail = new HashMap<>();
    private final Map<String, Coordinatore> byMatricola = new HashMap<>();
    private final Map<String, List<Coordinatore>> byCorso = new HashMap<>();
    private Coordinatore coordinatoreDaRitornare;

    public void add(Coordinatore c, String corsoLaurea) {
        byEmail.put(c.getEmail(), c);
        byMatricola.put(c.getMatricola(), c);

        byCorso.computeIfAbsent(corsoLaurea, k -> new ArrayList<>()).add(c);
    }

    @Override
    public Coordinatore trovaCoordinatoreUniClass(String matricola) {
        if (coordinatoreDaRitornare != null) {
            return coordinatoreDaRitornare;
        }
        return byMatricola.get(matricola);
    }

    @Override
    public Coordinatore trovaCoordinatoreEmailUniclass(String email) {
        if (coordinatoreDaRitornare != null) {
            return coordinatoreDaRitornare;
        }
        return byEmail.get(email);
    }

    @Override
    public List<Coordinatore> trovaCoordinatoriCorsoLaurea(String nomeCorso) {
        if (coordinatoreDaRitornare != null) {
            return Collections.singletonList(coordinatoreDaRitornare);
        }
        return byCorso.getOrDefault(nomeCorso, Collections.emptyList());
    }

    @Override
    public List<Coordinatore> trovaTutti() {
        if (coordinatoreDaRitornare != null) {
            return Collections.singletonList(coordinatoreDaRitornare);
        }
        return new ArrayList<>(byEmail.values());
    }

    @Override
    public void aggiungiCoordinatore(Coordinatore c) { }

    @Override
    public void rimuoviCoordinatore(Coordinatore c) { }

    public void setCoordinatoreDaRitornare(Coordinatore c) {
        this.coordinatoreDaRitornare=c;
    }
}
