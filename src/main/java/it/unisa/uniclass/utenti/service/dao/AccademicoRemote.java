package it.unisa.uniclass.utenti.service.dao;

import it.unisa.uniclass.utenti.model.*;
import jakarta.ejb.Remote;

import java.util.List;


@Remote
public interface AccademicoRemote {

    // CRUD di base
    void create(Accademico accademico);
    void update(Accademico accademico);
    void remove(Accademico accademico);


    // QUERY di retrieval
    List<Accademico> findByRole(Ruolo ruolo);
    List<Accademico> findByRuoloAndDipartimento(Ruolo ruolo, String dipartimento);
    List<Accademico> findAll();
    Accademico findByMatricola(String matricola);
}
