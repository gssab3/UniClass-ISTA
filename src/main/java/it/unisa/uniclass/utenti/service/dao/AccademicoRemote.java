package it.unisa.uniclass.utenti.service.dao;

import it.unisa.uniclass.utenti.model.*;
import it.unisa.uniclass.utenti.model.Docente;
import it.unisa.uniclass.utenti.model.Tipo;
import jakarta.ejb.Remote;

import java.util.List;


@Remote
public interface AccademicoRemote {

    // CRUD di base
    void create(Accademico accademico);
    void update(Accademico accademico);
    void remove(Accademico accademico);

    // Ricerca
    Accademico findByEmail(String email);
    Accademico findByMatricola(String matricola);

    // QUERY PARAMETRICHE
    // Sostituisce findAllStudenti, findAllDocenti, ecc.
    List<Accademico> findByRuolo(Ruolo ruolo);


    List<Accademico> findByRuoloAndDipartimento(Ruolo ruolo, String dipartimento);

    List<Accademico> findAll();
}
