package it.unisa.uniclass.testing.benchmark.jmh.utenti.mocks;

import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.service.dao.AccademicoRemote;
import java.util.Collections;
import java.util.List;

public class MockAccademicoDAO implements AccademicoRemote {

    private Accademico accademicoDaRitornare;

    public void setAccademicoDaRitornare(Accademico accademico) {
        this.accademicoDaRitornare = accademico;
    }

    @Override
    public Accademico trovaAccademicoUniClass(String matricola) {
        if (accademicoDaRitornare != null && matricola.equals("0512105555")) {
            return accademicoDaRitornare;
        }
        return null;
    }

    @Override
    public Accademico trovaEmailUniClass(String email) {
        if (accademicoDaRitornare != null && email.equals(accademicoDaRitornare.getEmail())) {
            return accademicoDaRitornare;
        }
        return null;
    }

    // Metodi dummy
    public List<Accademico> trovaTuttiUniClass() { return Collections.emptyList(); }
    public List<Accademico> trovaAttivati(boolean b) { return Collections.emptyList(); }
    public void aggiungiAccademico(Accademico a) {}
    public void rimuoviAccademico(Accademico a) {}
    public List<String> retrieveEmail() { return Collections.emptyList(); }
    public void cambiaAttivazione(Accademico a, boolean b) {}
}