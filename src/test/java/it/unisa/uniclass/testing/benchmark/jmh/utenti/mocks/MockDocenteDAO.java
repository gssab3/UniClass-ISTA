package it.unisa.uniclass.testing.benchmark.jmh.utenti.mocks;

import java.util.*;

public class MockDocenteDAO implements DocenteRemote {

    private final Map<String, Docente> byMatricola = new HashMap<>();
    private final Map<String, Docente> byEmail = new HashMap<>();
    private final Map<String, List<Docente>> byCorso = new HashMap<>();

    private Docente docenteDaRitornare;

    public void add(Docente d, String corsoLaurea) {
        byMatricola.put(d.getMatricola(), d);
        if (d.getEmail() != null)
            byEmail.put(d.getEmail(), d);

        byCorso.computeIfAbsent(corsoLaurea, c -> new ArrayList<>()).add(d);
    }

    public void clear() {
        byMatricola.clear();
        byEmail.clear();
        byCorso.clear();
    }

    @Override
    public Docente trovaDocenteUniClass(String matricola) {
        if (docenteDaRitornare != null) {
            return docenteDaRitornare;
        }
        return byMatricola.get(matricola);
    }

    @Override
    public Docente trovaEmailUniClass(String email) {
        if (docenteDaRitornare != null) {
            return docenteDaRitornare;
        }
        return byEmail.get(email);
    }

    @Override
    public List<Docente> trovaDocenteCorsoLaurea(String nomeCorso) {
        if (docenteDaRitornare != null) {
            return Collections.singletonList(docenteDaRitornare);
        }
        return byCorso.getOrDefault(nomeCorso, Collections.emptyList());
    }

    @Override
    public List<Docente> trovaTuttiUniClass() {
        if (docenteDaRitornare != null) {
            return Collections.singletonList(docenteDaRitornare);
        }
        return new ArrayList<>(byMatricola.values());
    }

    @Override
    public void aggiungiDocente(Docente d) { }

    @Override
    public void rimuoviDocente(Docente d) { }

    public void setDocenteDaRitornare(Docente d) {
        this.docenteDaRitornare=d;
    }
}
